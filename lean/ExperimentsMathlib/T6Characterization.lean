import Mathlib

/-!
# T6 Axiomatic characterization of the three criteria

Statements over a shared (aligned) context `α` are pairs `(H, C)`. We consider four closure
properties of a comparison relation `r`:

* `Sound`: `r R S` implies that the closures `∀ x, H x → C x` are equivalent;
* `Restrict`: `r R S` implies `r (R|P) (S|P)` for every predicate `P`, where `R|P` adds `P`
  to the hypotheses (a faithfulness judgement survives adding the same hypothesis on both
  sides);
* `VacRespect`: `r R S` implies that `R` and `S` are either both vacuous or both not;
* `WeakRespect`: `r R S` implies `r ⟨True, C_R⟩ ⟨True, C_S⟩` (the raw claims, with all
  hypotheses dropped, are again related).

The greatest relations satisfying the nested axiom sets are, in order,

    {Sound}                              → closed equivalence        `ClosedEquiv`
    {Sound, Restrict}                    → pointwise implication     `PointImp`
    {Sound, Restrict, VacRespect}        → conditional equivalence   `CondEquiv`
    {Sound, Restrict, VacRespect, Weak}  → component equivalence     `CompEquiv`

and the inclusions are strict (`strict_*`). The first two layers identify all true theorems
(`closedEquiv_of_true`, `pointImp_of_true`): vacuity respect is the first axiom that
separates true theorems, and between true theorems it does so exactly at hypothesis
differences (`T5.true_true_reject_iff`). Conditional extensionality of the conclusion is
incompatible with `{Sound, Restrict, WeakRespect}` on any context with a point outside the
hypotheses (`no_condExt`), which is the no-go theorem.
-/

namespace T6

structure Stmt (α : Type*) where
  H : α → Prop
  C : α → Prop

variable {α : Type*}

def Stmt.Closed (S : Stmt α) : Prop := ∀ x, S.H x → S.C x

/-- Add the hypothesis `P` on the context. -/
def Stmt.restrict (S : Stmt α) (P : α → Prop) : Stmt α := ⟨fun x => S.H x ∧ P x, S.C⟩

/-- Drop all hypotheses: the raw claim. -/
def Stmt.weaken (S : Stmt α) : Stmt α := ⟨fun _ => True, S.C⟩

def Stmt.Inhabited (S : Stmt α) : Prop := ∃ x, S.H x

/-! ## The four relations -/

def ClosedEquiv (R S : Stmt α) : Prop := R.Closed ↔ S.Closed

def PointImp (R S : Stmt α) : Prop := ∀ x, (R.H x → R.C x) ↔ (S.H x → S.C x)

def CondEquiv (R S : Stmt α) : Prop := ∀ x, (R.H x ↔ S.H x) ∧ (R.H x → (R.C x ↔ S.C x))

def CompEquiv (R S : Stmt α) : Prop := ∀ x, (R.H x ↔ S.H x) ∧ (R.C x ↔ S.C x)

/-! ## The axioms -/

def Sound (r : Stmt α → Stmt α → Prop) : Prop := ∀ R S, r R S → (R.Closed ↔ S.Closed)

def Restrict (r : Stmt α → Stmt α → Prop) : Prop :=
  ∀ R S (P : α → Prop), r R S → r (R.restrict P) (S.restrict P)

def VacRespect (r : Stmt α → Stmt α → Prop) : Prop :=
  ∀ R S, r R S → (R.Inhabited ↔ S.Inhabited)

def WeakRespect (r : Stmt α → Stmt α → Prop) : Prop :=
  ∀ R S, r R S → r R.weaken S.weaken

/-- Conditional extensionality of the conclusion over a fixed hypothesis. -/
def CondExt (r : Stmt α → Stmt α → Prop) : Prop :=
  ∀ (H C C' : α → Prop), (∀ x, H x → (C x ↔ C' x)) → r ⟨H, C⟩ ⟨H, C'⟩

/-! ## Basic facts about restriction to a point -/

theorem Stmt.closed_restrict_eq (S : Stmt α) (x : α) :
    (S.restrict (· = x)).Closed ↔ (S.H x → S.C x) := by
  constructor
  · intro h hx
    exact h x ⟨hx, rfl⟩
  · rintro h y ⟨hy, rfl⟩
    exact h hy

theorem Stmt.inhabited_restrict_eq (S : Stmt α) (x : α) :
    (S.restrict (· = x)).Inhabited ↔ S.H x :=
  ⟨fun ⟨_, hy, rfl⟩ => hy, fun hx => ⟨x, hx, rfl⟩⟩

/-! ## Layer 1: soundness alone gives closed equivalence -/

theorem le_closedEquiv {r : Stmt α → Stmt α → Prop} (hs : Sound r) {R S : Stmt α} (h : r R S) :
    ClosedEquiv R S := hs R S h

theorem closedEquiv_sound : Sound (ClosedEquiv (α := α)) := fun _ _ h => h

/-- Collapse: two true theorems are closed-equivalent. -/
theorem closedEquiv_of_true {R S : Stmt α} (hR : R.Closed) (hS : S.Closed) : ClosedEquiv R S :=
  ⟨fun _ => hS, fun _ => hR⟩

/-! ## Layer 2: soundness and restriction give pointwise implication -/

theorem le_pointImp {r : Stmt α → Stmt α → Prop} (hs : Sound r) (hr : Restrict r) {R S : Stmt α}
    (h : r R S) : PointImp R S := fun x => by
  have := hs _ _ (hr R S (· = x) h)
  rwa [R.closed_restrict_eq, S.closed_restrict_eq] at this

theorem pointImp_sound : Sound (PointImp (α := α)) := fun _ _ h =>
  ⟨fun hR x hx => (h x).1 (hR x) hx, fun hS x hx => (h x).2 (hS x) hx⟩

theorem pointImp_restrict : Restrict (PointImp (α := α)) := fun _ _ _ h x =>
  ⟨fun hR ⟨hx, px⟩ => (h x).1 (fun hx' => hR ⟨hx', px⟩) hx,
   fun hS ⟨hx, px⟩ => (h x).2 (fun hx' => hS ⟨hx', px⟩) hx⟩

/-- Still a collapse: pointwise implication identifies all true theorems. -/
theorem pointImp_of_true {R S : Stmt α} (hR : R.Closed) (hS : S.Closed) : PointImp R S :=
  fun x => ⟨fun _ => hS x, fun _ => hR x⟩

/-! ## Layer 3: adding vacuity respect gives conditional equivalence -/

theorem hyp_pointwise {r : Stmt α → Stmt α → Prop} (hr : Restrict r) (hv : VacRespect r)
    {R S : Stmt α} (h : r R S) (x : α) : R.H x ↔ S.H x := by
  have := hv _ _ (hr R S (· = x) h)
  rwa [R.inhabited_restrict_eq, S.inhabited_restrict_eq] at this

theorem le_condEquiv {r : Stmt α → Stmt α → Prop} (hs : Sound r) (hr : Restrict r)
    (hv : VacRespect r) {R S : Stmt α} (h : r R S) : CondEquiv R S := fun x => by
  have hH := hyp_pointwise hr hv h x
  have hI := le_pointImp hs hr h x
  refine ⟨hH, fun hx => ⟨fun hc => hI.1 (fun _ => hc) (hH.1 hx), fun hc => hI.2 (fun _ => hc) hx⟩⟩

theorem condEquiv_sound : Sound (CondEquiv (α := α)) := fun _ _ h =>
  ⟨fun hR x hx => ((h x).2 ((h x).1.2 hx)).1 (hR x ((h x).1.2 hx)),
   fun hS x hx => ((h x).2 hx).2 (hS x ((h x).1.1 hx))⟩

theorem condEquiv_restrict : Restrict (CondEquiv (α := α)) := fun _ _ _ h x =>
  ⟨⟨fun ⟨hx, px⟩ => ⟨(h x).1.1 hx, px⟩, fun ⟨hx, px⟩ => ⟨(h x).1.2 hx, px⟩⟩,
   fun ⟨hx, _⟩ => (h x).2 hx⟩

theorem condEquiv_vacRespect : VacRespect (CondEquiv (α := α)) := fun _ _ h =>
  ⟨fun ⟨x, hx⟩ => ⟨x, (h x).1.1 hx⟩, fun ⟨x, hx⟩ => ⟨x, (h x).1.2 hx⟩⟩

/-- Between true theorems the only possible difference is in the hypotheses. -/
theorem condEquiv_true_true_iff {R S : Stmt α} (hR : R.Closed) (hS : S.Closed) :
    CondEquiv R S ↔ ∀ x, (R.H x ↔ S.H x) :=
  ⟨fun h x => (h x).1, fun h x => ⟨h x, fun hx => ⟨fun _ => hS x ((h x).1 hx), fun _ => hR x hx⟩⟩⟩

/-! ## Layer 4: adding weakening respect gives component equivalence -/

theorem conc_pointwise {r : Stmt α → Stmt α → Prop} (hs : Sound r) (hr : Restrict r)
    (hw : WeakRespect r) {R S : Stmt α} (h : r R S) (x : α) : R.C x ↔ S.C x := by
  have := le_pointImp hs hr (hw R S h) x
  simpa [Stmt.weaken] using this

theorem le_compEquiv {r : Stmt α → Stmt α → Prop} (hs : Sound r) (hr : Restrict r)
    (hv : VacRespect r) (hw : WeakRespect r) {R S : Stmt α} (h : r R S) : CompEquiv R S :=
  fun x => ⟨hyp_pointwise hr hv h x, conc_pointwise hs hr hw h x⟩

theorem compEquiv_cond {R S : Stmt α} (h : CompEquiv R S) : CondEquiv R S :=
  fun x => ⟨(h x).1, fun _ => (h x).2⟩

theorem compEquiv_sound : Sound (CompEquiv (α := α)) := fun R S h =>
  condEquiv_sound R S (compEquiv_cond h)

theorem compEquiv_restrict : Restrict (CompEquiv (α := α)) := fun _ _ _ h x =>
  ⟨⟨fun ⟨hx, px⟩ => ⟨(h x).1.1 hx, px⟩, fun ⟨hx, px⟩ => ⟨(h x).1.2 hx, px⟩⟩, (h x).2⟩

theorem compEquiv_vacRespect : VacRespect (CompEquiv (α := α)) := fun R S h =>
  condEquiv_vacRespect R S (compEquiv_cond h)

theorem compEquiv_weakRespect : WeakRespect (CompEquiv (α := α)) := fun _ _ h x =>
  ⟨Iff.rfl, (h x).2⟩

/-! ## Inclusions -/

theorem condEquiv_pointImp {R S : Stmt α} (h : CondEquiv R S) : PointImp R S := fun x =>
  ⟨fun hR hx => ((h x).2 ((h x).1.2 hx)).1 (hR ((h x).1.2 hx)),
   fun hS hx => ((h x).2 hx).2 (hS ((h x).1.1 hx))⟩

theorem pointImp_closedEquiv {R S : Stmt α} (h : PointImp R S) : ClosedEquiv R S :=
  pointImp_sound R S h

/-! ## Strictness, on the context `Bool` -/

/-- `b = true → True` versus `b = true → b = true`: conditionally but not component equivalent
(off-domain). -/
theorem strict_comp_cond :
    CondEquiv (⟨fun b => b = true, fun _ => True⟩ : Stmt Bool) ⟨fun b => b = true, fun b => b = true⟩ ∧
    ¬ CompEquiv (⟨fun b => b = true, fun _ => True⟩ : Stmt Bool) ⟨fun b => b = true, fun b => b = true⟩ := by
  refine ⟨fun b => ⟨Iff.rfl, fun hb => ⟨fun _ => hb, fun _ => trivial⟩⟩, fun h => ?_⟩
  have := (h false).2
  simp at this

/-- The vacuous statement versus the trivially true statement: pointwise-implication equivalent
but not conditionally equivalent. -/
theorem strict_cond_pointImp :
    PointImp (⟨fun _ => False, fun _ => False⟩ : Stmt Bool) ⟨fun _ => True, fun _ => True⟩ ∧
    ¬ CondEquiv (⟨fun _ => False, fun _ => False⟩ : Stmt Bool) ⟨fun _ => True, fun _ => True⟩ := by
  refine ⟨fun _ => ⟨fun _ _ => trivial, fun _ h => h.elim⟩, fun h => ?_⟩
  exact (h true).1.2 trivial

/-- Two false statements: closed-equivalent but not pointwise-implication equivalent. -/
theorem strict_pointImp_closed :
    ClosedEquiv (⟨fun _ => True, fun b => b = true⟩ : Stmt Bool) ⟨fun _ => True, fun b => b = false⟩ ∧
    ¬ PointImp (⟨fun _ => True, fun b => b = true⟩ : Stmt Bool) ⟨fun _ => True, fun b => b = false⟩ := by
  refine ⟨⟨fun h => absurd (h false trivial) (by decide), fun h => absurd (h true trivial) (by decide)⟩,
    fun h => ?_⟩
  have := (h true).1 (fun _ => rfl) trivial
  exact Bool.noConfusion this

/-! ## No-go: conditional extensionality is incompatible with the component axioms -/

/-- On any context with a point `x₀` outside some hypothesis `H`, no relation satisfies
`Sound`, `Restrict`, `WeakRespect` and `CondExt` simultaneously. -/
theorem no_condExt {r : Stmt α → Stmt α → Prop} (hs : Sound r) (hr : Restrict r)
    (hw : WeakRespect r) (he : CondExt r) {H : α → Prop} {x₀ : α} (hx : ¬ H x₀) : False := by
  have h := he H (fun _ => True) H (fun x hx => ⟨fun _ => hx, fun _ => trivial⟩)
  exact hx ((conc_pointwise hs hr hw h x₀).1 trivial)

theorem no_condExt_bool : ¬ ∃ r : Stmt Bool → Stmt Bool → Prop,
    Sound r ∧ Restrict r ∧ WeakRespect r ∧ CondExt r := by
  rintro ⟨r, hs, hr, hw, he⟩
  exact no_condExt hs hr hw he (H := fun b => b = true) (x₀ := false) (by decide)

/-- Dropping `WeakRespect` the four-axiom set is consistent: `CondEquiv` satisfies `CondExt`. -/
theorem condEquiv_condExt : CondExt (CondEquiv (α := α)) := fun _ _ _ h x => ⟨Iff.rfl, h x⟩

/-! ## Forced separations

Restriction and vacuity respect alone (no soundness needed) separate two statements as soon as
their hypotheses differ at one point. Two consequences a human reader often tolerates: a
decorative hypothesis that fails only where the conclusion holds anyway, and the contrapositive
presentation, which is pointwise-implication equivalent. -/

theorem forced_sep {r : Stmt α → Stmt α → Prop} (hr : Restrict r) (hv : VacRespect r)
    {R S : Stmt α} {x : α} (hx : ¬ (R.H x ↔ S.H x)) : ¬ r R S :=
  fun h => hx (hyp_pointwise hr hv h x)

theorem forced_sep_decorative {r : Stmt α → Stmt α → Prop} (hr : Restrict r) (hv : VacRespect r)
    (H C D : α → Prop) {x : α} (hx : H x) (hd : ¬ D x) :
    ¬ r ⟨H, C⟩ ⟨fun y => H y ∧ D y, C⟩ :=
  forced_sep hr hv (x := x) fun h => hd (h.1 hx).2

theorem contra_pointImp (H C : α → Prop) :
    PointImp ⟨H, C⟩ ⟨fun y => ¬ C y, fun y => ¬ H y⟩ :=
  fun _ => not_imp_not.symm

theorem forced_sep_contra {r : Stmt α → Stmt α → Prop} (hr : Restrict r) (hv : VacRespect r)
    (H C : α → Prop) {x : α} (hx : ¬ (H x ↔ ¬ C x)) :
    ¬ r ⟨H, C⟩ ⟨fun y => ¬ C y, fun y => ¬ H y⟩ :=
  forced_sep hr hv hx

/-! ## Directions, vacuity-only rejects and reference transport

A reject that is still `PointImp` differs only in vacuity: both statements make the same claim
at every point, and only the set of points where the claim is vacuous moves. The two forced
separations above are of this kind, the decorative one as soon as the conclusion holds wherever
the extra hypothesis fails. Outside `PointImp`, one-sided pointwise implication gives the direction
of the difference. -/

/-- `S` is pointwise implied by `R`: whatever `R` claims at a point, `S` claims at most. -/
def PtLe (R S : Stmt α) : Prop := ∀ x, (R.H x → R.C x) → (S.H x → S.C x)

theorem closed_of_ptLe {R S : Stmt α} (h : PtLe R S) (hR : R.Closed) : S.Closed :=
  fun x => h x (hR x)

theorem pointImp_iff_ptLe {R S : Stmt α} : PointImp R S ↔ PtLe R S ∧ PtLe S R :=
  ⟨fun h => ⟨fun x => (h x).1, fun x => (h x).2⟩, fun h x => ⟨h.1 x, h.2 x⟩⟩

/-- Adding a hypothesis always weakens the claim pointwise. -/
theorem ptLe_restrict (S : Stmt α) (P : α → Prop) : PtLe S (S.restrict P) :=
  fun _ h hx => h hx.1

/-- A decorative hypothesis is vacuity-only when the conclusion holds where it fails. -/
theorem decorative_pointImp (H C D : α → Prop) (hd : ∀ x, H x → ¬ D x → C x) :
    PointImp ⟨H, C⟩ ⟨fun y => H y ∧ D y, C⟩ := fun x =>
  ⟨fun h hx => h hx.1, fun h hx => by
    by_cases d : D x
    · exact h ⟨hx, d⟩
    · exact hd x hx d⟩

/-- A vacuity-only reject: hypotheses differ somewhere, the pointwise claims nowhere. -/
theorem vacuity_only_reject {R S : Stmt α} (hp : PointImp R S) {x : α} (hx : ¬ (R.H x ↔ S.H x)) :
    PointImp R S ∧ ¬ CondEquiv R S :=
  ⟨hp, fun h => hx (h x).1⟩

/-- Every reject of a pointwise-equivalent pair is a hypothesis difference. -/
theorem pointImp_not_cond_hyp {R S : Stmt α} (hp : PointImp R S) (hn : ¬ CondEquiv R S) :
    ∃ x, ¬ (R.H x ↔ S.H x) := by
  by_contra h
  push_neg at h
  refine hn fun x => ⟨h x, fun hx => ⟨fun hc => (hp x).1 (fun _ => hc) ((h x).1 hx),
    fun hc => (hp x).2 (fun _ => hc) hx⟩⟩

/-- All four relations are equivalence relations. -/
theorem compEquiv_equivalence : Equivalence (CompEquiv (α := α)) :=
  ⟨fun _ _ => ⟨Iff.rfl, Iff.rfl⟩, fun h x => ⟨(h x).1.symm, (h x).2.symm⟩,
   fun h k x => ⟨(h x).1.trans (k x).1, (h x).2.trans (k x).2⟩⟩

theorem condEquiv_equivalence : Equivalence (CondEquiv (α := α)) :=
  ⟨fun _ _ => ⟨Iff.rfl, fun _ => Iff.rfl⟩,
   fun h x => ⟨(h x).1.symm, fun hx => ((h x).2 ((h x).1.2 hx)).symm⟩,
   fun h k x => ⟨(h x).1.trans (k x).1, fun hx => ((h x).2 hx).trans ((k x).2 ((h x).1.1 hx))⟩⟩

/-- Reference transport: replacing the reference by an accepted one changes no verdict. -/
theorem transport_comp {R R' S : Stmt α} (h : CompEquiv R R') : CompEquiv R S ↔ CompEquiv R' S :=
  ⟨compEquiv_equivalence.trans (compEquiv_equivalence.symm h),
   compEquiv_equivalence.trans h⟩

theorem transport_cond {R R' S : Stmt α} (h : CompEquiv R R') : CondEquiv R S ↔ CondEquiv R' S :=
  ⟨condEquiv_equivalence.trans (condEquiv_equivalence.symm (compEquiv_cond h)),
   condEquiv_equivalence.trans (compEquiv_cond h)⟩

/-- The decided verdicts are mutually exclusive. -/
theorem accept_not_reject {R S : Stmt α} (h : CompEquiv R S) : ¬ ¬ CondEquiv R S :=
  fun hn => hn (compEquiv_cond h)

end T6

#print axioms T6.le_compEquiv
#print axioms T6.le_condEquiv
#print axioms T6.pointImp_of_true
#print axioms T6.no_condExt_bool
#print axioms T6.strict_comp_cond
#print axioms T6.strict_cond_pointImp
#print axioms T6.strict_pointImp_closed
#print axioms T6.forced_sep_decorative
#print axioms T6.forced_sep_contra
#print axioms T6.contra_pointImp
#print axioms T6.decorative_pointImp
#print axioms T6.pointImp_not_cond_hyp
#print axioms T6.transport_cond
#print axioms T6.closed_of_ptLe
