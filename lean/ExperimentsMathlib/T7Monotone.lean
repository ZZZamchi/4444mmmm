import Mathlib

/-!
# T7 Prover strength and false accepts

A prover is modelled by the set `O : Prop → Prop` of propositions it can establish; it is
sound when `O p → p`, and stronger provers have larger `O`. Closed equivalence accepts a pair
when the prover establishes `Cl R ↔ Cl S`; the three-valued criterion accepts when the prover
establishes the two component goals and rejects when it refutes conditional equivalence.

* `closedAcc_mono`, `compAcc_mono`, `compRej_mono`: all three accept/reject sets grow with the
  prover; `unknown_anti`: the unknown set shrinks.
* `closedFA_mono`, `closedFA_limit`: the false accepts of closed equivalence grow with the
  prover, and in the limit (the complete prover) contain every unfaithful pair whose two
  closures have the same truth value, in particular every unfaithful true candidate.
* `compFA_bounded`, `compFA_empty`: the false accepts of the three-valued criterion are
  bounded, for every sound prover, by the unfaithful component-equivalent pairs; if the labels
  respect component equivalence this bound is empty.
* `closedFA_strict`: the growth is strict as soon as there is an unfaithful true candidate.
-/

namespace T7

structure Stmt (α : Type*) where
  H : α → Prop
  C : α → Prop

variable {α : Type*}

def Stmt.Closed (S : Stmt α) : Prop := ∀ x, S.H x → S.C x

def CondEquiv (R S : Stmt α) : Prop := ∀ x, (R.H x ↔ S.H x) ∧ (R.H x → (R.C x ↔ S.C x))

def CompEquiv (R S : Stmt α) : Prop := ∀ x, (R.H x ↔ S.H x) ∧ (R.C x ↔ S.C x)

/-- A prover: the propositions it can establish. `O ≤ O'` is pointwise implication. -/
abbrev Oracle := Prop → Prop

def Oracle.Sound (O : Oracle) : Prop := ∀ p, O p → p

/-- The complete prover. -/
def Oracle.truth : Oracle := fun p => p

/-- The prover that proves nothing. -/
def Oracle.none : Oracle := fun _ => False

theorem Oracle.truth_sound : Oracle.truth.Sound := fun _ h => h

theorem Oracle.none_sound : Oracle.none.Sound := fun _ h => h.elim

theorem Oracle.none_le (O : Oracle) : Oracle.none ≤ O := fun _ h => h.elim

theorem Oracle.le_truth {O : Oracle} (hO : O.Sound) : O ≤ Oracle.truth := hO

/-! ## Verdicts under a prover -/

def closedAcc (O : Oracle) (R S : Stmt α) : Prop := O (R.Closed ↔ S.Closed)

def compAcc (O : Oracle) (R S : Stmt α) : Prop :=
  O (∀ x, R.H x ↔ S.H x) ∧ O (∀ x, R.C x ↔ S.C x)

def compRej (O : Oracle) (R S : Stmt α) : Prop := O (¬ CondEquiv R S)

def unknown (O : Oracle) (R S : Stmt α) : Prop := ¬ compAcc O R S ∧ ¬ compRej O R S

/-! ## Monotonicity in the prover -/

theorem closedAcc_mono {O O' : Oracle} (h : O ≤ O') {R S : Stmt α} :
    closedAcc O R S → closedAcc O' R S := h _

theorem compAcc_mono {O O' : Oracle} (h : O ≤ O') {R S : Stmt α} :
    compAcc O R S → compAcc O' R S := fun ⟨a, b⟩ => ⟨h _ a, h _ b⟩

theorem compRej_mono {O O' : Oracle} (h : O ≤ O') {R S : Stmt α} :
    compRej O R S → compRej O' R S := h _

theorem unknown_anti {O O' : Oracle} (h : O ≤ O') {R S : Stmt α} :
    unknown O' R S → unknown O R S := fun ⟨a, b⟩ =>
  ⟨fun c => a (compAcc_mono h c), fun c => b (compRej_mono h c)⟩

/-! ## Soundness of the verdicts -/

theorem closedAcc_sound {O : Oracle} (hO : O.Sound) {R S : Stmt α} (h : closedAcc O R S) :
    R.Closed ↔ S.Closed := hO _ h

theorem compAcc_sound {O : Oracle} (hO : O.Sound) {R S : Stmt α} (h : compAcc O R S) :
    CompEquiv R S := fun x => ⟨hO _ h.1 x, hO _ h.2 x⟩

theorem compRej_sound {O : Oracle} (hO : O.Sound) {R S : Stmt α} (h : compRej O R S) :
    ¬ CondEquiv R S := hO _ h

/-- Accepting at the component level implies accepting at the closed level, for the complete
prover: the three-valued criterion is never more permissive. -/
theorem compAcc_closedAcc_truth {R S : Stmt α} (h : compAcc Oracle.truth R S) :
    closedAcc Oracle.truth R S := by
  have hc := compAcc_sound Oracle.truth_sound h
  exact ⟨fun hR x hx => (hc x).2.1 (hR x ((hc x).1.2 hx)),
    fun hS x hx => (hc x).2.2 (hS x ((hc x).1.1 hx))⟩

/-! ## False accepts against a label -/

/-- Pairs labelled unfaithful by `L` that the verdict `acc` accepts. -/
def FA (acc : Stmt α → Stmt α → Prop) (L : Stmt α → Stmt α → Prop) : Set (Stmt α × Stmt α) :=
  {p | ¬ L p.1 p.2 ∧ acc p.1 p.2}

theorem closedFA_mono {O O' : Oracle} (h : O ≤ O') (L : Stmt α → Stmt α → Prop) :
    FA (closedAcc O) L ⊆ FA (closedAcc O') L := fun _ ⟨hl, ha⟩ => ⟨hl, closedAcc_mono h ha⟩

theorem compFA_mono {O O' : Oracle} (h : O ≤ O') (L : Stmt α → Stmt α → Prop) :
    FA (compAcc O) L ⊆ FA (compAcc O') L := fun _ ⟨hl, ha⟩ => ⟨hl, compAcc_mono h ha⟩

/-- In the limit, closed equivalence false-accepts every unfaithful pair whose closures share
a truth value. -/
theorem closedFA_limit (L : Stmt α → Stmt α → Prop) :
    {p : Stmt α × Stmt α | ¬ L p.1 p.2 ∧ (p.1.Closed ↔ p.2.Closed)} ⊆ FA (closedAcc Oracle.truth) L :=
  fun _ h => h

/-- In particular every unfaithful true candidate. -/
theorem closedFA_true_true (L : Stmt α → Stmt α → Prop) {R S : Stmt α} (hl : ¬ L R S)
    (hR : R.Closed) (hS : S.Closed) : (R, S) ∈ FA (closedAcc Oracle.truth) L :=
  ⟨hl, fun _ => hS, fun _ => hR⟩

/-- For every sound prover, the false accepts of the three-valued criterion lie inside the
unfaithful component-equivalent pairs, a set that does not depend on the prover. -/
theorem compFA_bounded {O : Oracle} (hO : O.Sound) (L : Stmt α → Stmt α → Prop) :
    FA (compAcc O) L ⊆ {p | ¬ L p.1 p.2 ∧ CompEquiv p.1 p.2} :=
  fun _ ⟨hl, ha⟩ => ⟨hl, compAcc_sound hO ha⟩

/-- If the labels respect component equivalence, no sound prover produces a false accept. -/
theorem compFA_empty {O : Oracle} (hO : O.Sound) {L : Stmt α → Stmt α → Prop}
    (hL : ∀ R S, CompEquiv R S → L R S) : FA (compAcc O) L = ∅ := by
  ext p
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨hl, ha⟩
  exact hl (hL _ _ (compAcc_sound hO ha))

/-! ## Strictness -/

/-- An unfaithful true candidate is missed by the empty prover and false-accepted by the
complete one; hence the closed false-accept set grows strictly with the prover. -/
theorem closedFA_strict (L : Stmt α → Stmt α → Prop) {R S : Stmt α} (hl : ¬ L R S)
    (hR : R.Closed) (hS : S.Closed) :
    (R, S) ∉ FA (closedAcc Oracle.none) L ∧ (R, S) ∈ FA (closedAcc Oracle.truth) L :=
  ⟨fun h => h.2, closedFA_true_true L hl hR hS⟩

/-- A concrete instance on `Bool` with `L := CompEquiv`: the reference `b = true → b = true`
and the candidate `b = true → True` (junk conclusion outside the hypothesis). -/
def ref : Stmt Bool := ⟨fun b => b = true, fun b => b = true⟩
def cand : Stmt Bool := ⟨fun b => b = true, fun _ => True⟩

theorem ref_cand_not_comp : ¬ CompEquiv ref cand := fun h => by
  have := (h false).2
  simp [ref, cand] at this

theorem ref_cand_closed_strict :
    (ref, cand) ∉ FA (closedAcc Oracle.none) CompEquiv ∧
    (ref, cand) ∈ FA (closedAcc Oracle.truth) CompEquiv :=
  closedFA_strict CompEquiv ref_cand_not_comp (fun _ h => h) (fun _ _ => trivial)

theorem ref_cand_comp_never {O : Oracle} (hO : O.Sound) :
    (ref, cand) ∉ FA (compAcc O) CompEquiv := by
  rw [compFA_empty hO (fun _ _ h => h)]
  exact Set.notMem_empty _

end T7

#print axioms T7.closedFA_mono
#print axioms T7.closedFA_limit
#print axioms T7.compFA_bounded
#print axioms T7.compFA_empty
#print axioms T7.unknown_anti
#print axioms T7.ref_cand_closed_strict
#print axioms T7.ref_cand_comp_never
