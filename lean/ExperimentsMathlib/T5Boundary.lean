import Mathlib

/-!
# Boundary degeneracies and embedding alignments

* `peelNeg_comp`: if the final negation of the conclusion is peeled into the hypotheses,
  `(Γ, H, ¬ Q) ↦ (Γ, H ∧ Q, False)`, any two true statements over the same context become
  component-equivalent, because both hypotheses are nowhere satisfiable.
* `trivialHyp_comp`: with no hypotheses on the shared context, two conclusions that hold
  everywhere are component-equivalent. No extensional comparison over that context can
  separate them.
* `residue_comp`: the same reduction for the closed remainder left in the conclusion by a
  partial alignment.
* `informative_iff`: a conclusion that is neither constantly true nor constantly false on the
  context is exactly one whose component class excludes both trivial conclusions
  `(Γ, H, True)` and `(Γ, H, False)`; closed comparison accepts `(Γ, H, True)` whenever the
  statement is true (`closed_top_iff`).
* `comp_absorb_iff`, `hypExt_absorb`: the absorption `(Γ, H ∧ C, C)` of a true statement is
  component-equivalent to it, closed by projection, and as informative as it; no relation that
  only looks at hypotheses up to pointwise equivalence can separate the two.
* Embedding alignments `e : Γ_S → Γ_R` (for instance `ℕ ↪ ℤ`): conditional equivalence
  along `e` gives `Cl R → Cl S` but not the converse; the converse holds when `e` covers
  the hypotheses of `R` (`along_closed_iff`). A point of `H_R` outside the range of `e` where
  `C_R` fails separates the closures (`off_image`).
-/

namespace T5

structure Stmt (α : Type*) where
  H : α → Prop
  C : α → Prop

variable {α β : Type*}

def Stmt.Closed (S : Stmt α) : Prop := ∀ x, S.H x → S.C x

def CompEquiv (R S : Stmt α) : Prop := ∀ x, (R.H x ↔ S.H x) ∧ (R.C x ↔ S.C x)

def CondEquiv (R S : Stmt α) : Prop := ∀ x, (R.H x ↔ S.H x) ∧ (R.H x → (R.C x ↔ S.C x))

/-- Between two true statements, a refutation of conditional equivalence is exactly a point
where the hypotheses differ; the conclusions cannot help. -/
theorem true_true_reject_iff {R S : Stmt α} (hR : R.Closed) (hS : S.Closed) :
    ¬ CondEquiv R S ↔ ∃ x, ¬ (R.H x ↔ S.H x) := by
  constructor
  · intro h
    by_contra hne
    push_neg at hne
    exact h fun x => ⟨hne x, fun hx => ⟨fun _ => hS x ((hne x).1 hx), fun _ => hR x hx⟩⟩
  · rintro ⟨x, hx⟩ h
    exact hx (h x).1

def peelNeg (H Q : α → Prop) : Stmt α := ⟨fun x => H x ∧ Q x, fun _ => False⟩

theorem peelNeg_closed (H Q : α → Prop) : (peelNeg H Q).Closed ↔ ∀ x, H x → ¬ Q x :=
  ⟨fun h x hx hq => h x ⟨hx, hq⟩, fun h x hx => h x hx.1 hx.2⟩

theorem peelNeg_comp {H Q H' Q' : α → Prop} (hR : ∀ x, H x → ¬ Q x) (hS : ∀ x, H' x → ¬ Q' x) :
    CompEquiv (peelNeg H Q) (peelNeg H' Q') := fun x =>
  ⟨⟨fun h => absurd h.2 (hR x h.1), fun h => absurd h.2 (hS x h.1)⟩, Iff.rfl⟩

theorem trivialHyp_comp {C C' : α → Prop} (h : ∀ x, C x) (h' : ∀ x, C' x) :
    CompEquiv ⟨fun _ => True, C⟩ ⟨fun _ => True, C'⟩ := fun x =>
  ⟨Iff.rfl, ⟨fun _ => h' x, fun _ => h x⟩⟩

/-- Residual collapse: when both conclusions hold at every point of the shared context (for
instance because each is a true closed remainder `∀ y, H' x y → C' x y` left by a partial
alignment), component equivalence reduces to equivalence of the hypotheses, whatever the
remainders are. -/
theorem residue_comp {R S : Stmt α} (hR : ∀ x, R.C x) (hS : ∀ x, S.C x) :
    CompEquiv R S ↔ ∀ x, R.H x ↔ S.H x :=
  ⟨fun h x => (h x).1, fun h x => ⟨h x, ⟨fun _ => hS x, fun _ => hR x⟩⟩⟩

/-- Two unrelated true remainders over an unaligned binder `m` are identified. -/
example : CompEquiv (⟨fun n : ℕ => 0 < n, fun _ => ∀ m : ℕ, m + 0 = m⟩ : Stmt ℕ)
    ⟨fun n => 0 < n, fun n => ∀ m : ℕ, m < n → 0 * m = 0⟩ :=
  (residue_comp (fun _ m => Nat.add_zero m) (fun _ m _ => Nat.zero_mul m)).2 fun _ => Iff.rfl

/-- The conclusion is neither true everywhere nor false everywhere on the shared context. -/
def Informative (R : Stmt α) : Prop := (¬ ∀ x, R.C x) ∧ ¬ ∀ x, ¬ R.C x

def topStmt (R : Stmt α) : Stmt α := ⟨R.H, fun _ => True⟩

def botStmt (R : Stmt α) : Stmt α := ⟨R.H, fun _ => False⟩

/-- Closed comparison accepts the trivial conclusion exactly when `R` is true. -/
theorem closed_top_iff (R : Stmt α) : (R.Closed ↔ (topStmt R).Closed) ↔ R.Closed :=
  ⟨fun h => h.2 fun _ _ => trivial, fun h => ⟨fun _ _ _ => trivial, fun _ => h⟩⟩

/-- An informative conclusion refutes component equivalence with every statement whose
conclusion is constant on the context, whatever its hypotheses. -/
theorem informative_rejects_constant {R S : Stmt α} (hi : Informative R)
    (hS : (∀ x, S.C x) ∨ ∀ x, ¬ S.C x) : ¬ CompEquiv R S := fun h =>
  hS.elim (fun hs => hi.1 fun x => (h x).2.2 (hs x)) fun hs => hi.2 fun x hr => hs x ((h x).2.1 hr)

/-- Informativeness is exactly the rejection of both trivial conclusions. -/
theorem informative_iff (R : Stmt α) :
    Informative R ↔ ¬ CompEquiv R (topStmt R) ∧ ¬ CompEquiv R (botStmt R) := by
  refine ⟨fun hi => ⟨informative_rejects_constant hi (.inl fun _ => trivial),
    informative_rejects_constant hi (.inr fun _ h => h)⟩, fun ⟨ht, hb⟩ => ⟨fun hc => ht ?_, fun hc => hb ?_⟩⟩
  · exact fun x => ⟨Iff.rfl, ⟨fun _ => trivial, fun _ => hc x⟩⟩
  · exact fun x => ⟨Iff.rfl, ⟨fun h => hc x h, False.elim⟩⟩

/-- Informativeness is a property of the component class. -/
theorem informative_of_comp {R S : Stmt α} (h : CompEquiv R S) (hi : Informative R) :
    Informative S :=
  ⟨fun hs => hi.1 fun x => (h x).2.2 (hs x), fun hs => hi.2 fun x hr => hs x ((h x).2.1 hr)⟩

/-- The absorption of `R`: its conclusion is added to its hypotheses. -/
def absorb (R : Stmt α) : Stmt α := ⟨fun x => R.H x ∧ R.C x, R.C⟩

/-- The absorption is closed by projection, whatever `R` is. -/
theorem absorb_closed (R : Stmt α) : (absorb R).Closed := fun _ h => h.2

/-- A statement is component-equivalent to its absorption exactly when it is true. -/
theorem comp_absorb_iff (R : Stmt α) : CompEquiv R (absorb R) ↔ R.Closed :=
  ⟨fun h x hx => ((h x).1.mp hx).2,
   fun h x => ⟨⟨fun hx => ⟨hx, h x hx⟩, And.left⟩, Iff.rfl⟩⟩

/-- Informativeness does not see absorption: the conclusion is unchanged. -/
theorem informative_absorb (R : Stmt α) : Informative (absorb R) ↔ Informative R := Iff.rfl

/-- No relation that is invariant under pointwise-equivalent hypotheses separates a true
statement from its absorption. -/
theorem hypExt_absorb (r : Stmt α → Stmt α → Prop)
    (ext : ∀ H H' C, (∀ x, H x ↔ H' x) → r ⟨H, C⟩ ⟨H', C⟩) (R : Stmt α) (hR : R.Closed) :
    r R (absorb R) :=
  ext R.H _ R.C fun x => ⟨fun hx => ⟨hx, hR x hx⟩, And.left⟩

/-- An informative true statement whose absorption is accepted. -/
example : CompEquiv (⟨fun n : ℕ => 4 ∣ n, fun n => 2 ∣ n⟩ : Stmt ℕ)
    (absorb ⟨fun n : ℕ => 4 ∣ n, fun n => 2 ∣ n⟩) ∧
    Informative (⟨fun n : ℕ => 4 ∣ n, fun n => 2 ∣ n⟩ : Stmt ℕ) := by
  refine ⟨(comp_absorb_iff _).2 fun n h => dvd_trans ⟨2, rfl⟩ h, ?_, ?_⟩
  · intro h; exact absurd (h 1) (by decide)
  · intro h; exact h 0 (dvd_zero 2)

/-- Conditional equivalence of `S` over `β` with `R` over `α` along `e : β → α`. -/
def Along (e : β → α) (R : Stmt α) (S : Stmt β) : Prop :=
  ∀ y, (S.H y ↔ R.H (e y)) ∧ (S.H y → (S.C y ↔ R.C (e y)))

theorem along_closed_mp {e : β → α} {R : Stmt α} {S : Stmt β} (h : Along e R S) :
    R.Closed → S.Closed := fun hR y hy =>
  ((h y).2 hy).2 (hR (e y) ((h y).1.1 hy))

theorem along_closed_iff {e : β → α} {R : Stmt α} {S : Stmt β} (h : Along e R S)
    (cover : ∀ x, R.H x → ∃ y, e y = x) : R.Closed ↔ S.Closed := by
  refine ⟨along_closed_mp h, fun hS x hx => ?_⟩
  obtain ⟨y, rfl⟩ := cover x hx
  exact ((h y).2 ((h y).1.2 hx)).1 (hS y ((h y).1.2 hx))

theorem off_image {e : β → α} {R : Stmt α} {S : Stmt β} (h : Along e R S) (hS : S.Closed)
    {x : α} (hx : R.H x) (hc : ¬ R.C x) : ¬ (R.Closed ↔ S.Closed) ∧ x ∉ Set.range e := by
  refine ⟨fun hiff => hc (hiff.2 hS x hx), ?_⟩
  rintro ⟨y, rfl⟩
  exact hc (((h y).2 ((h y).1.2 hx)).1 (hS y ((h y).1.2 hx)))

/-- Example: `∀ a : ℤ, 0 ≤ a` restricted along `ℕ ↪ ℤ` is the true `∀ n : ℕ, 0 ≤ (n : ℤ)`. -/
def intNonneg : Stmt ℤ := ⟨fun _ => True, fun a => 0 ≤ a⟩
def natNonneg : Stmt ℕ := ⟨fun _ => True, fun n => 0 ≤ (n : ℤ)⟩

theorem nat_along : Along (fun n : ℕ => (n : ℤ)) intNonneg natNonneg := fun _ =>
  ⟨Iff.rfl, fun _ => Iff.rfl⟩

theorem nat_off_image :
    ¬ (intNonneg.Closed ↔ natNonneg.Closed) ∧ (-1 : ℤ) ∉ Set.range (fun n : ℕ => (n : ℤ)) :=
  off_image nat_along (fun n _ => Int.natCast_nonneg n) trivial (show ¬ (0 : ℤ) ≤ -1 by decide)

end T5

#print axioms T5.true_true_reject_iff
#print axioms T5.peelNeg_comp
#print axioms T5.trivialHyp_comp
#print axioms T5.residue_comp
#print axioms T5.closed_top_iff
#print axioms T5.informative_rejects_constant
#print axioms T5.informative_iff
#print axioms T5.informative_of_comp
#print axioms T5.comp_absorb_iff
#print axioms T5.hypExt_absorb
#print axioms T5.along_closed_iff
#print axioms T5.nat_off_image
