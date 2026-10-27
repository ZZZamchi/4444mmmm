import Mathlib

/-!
# Representation invariance forces closed collapse

A statement is a telescope `(Γ, H, C)` with its own context type. A comparison relation
that is invariant under the usual re-presentations of a Lean statement

* moving the hypotheses into the conclusion (`curry`),
* folding the context into a universally quantified sentence (`fold`),
* replacing a sentence by an equivalent one (`ext`),

contains closed equivalence, so it identifies all true theorems. Component comparison
under an alignment is not `curry`-invariant (`alignedCond_not_curry`), which is why it
needs an alignment as input.
-/

namespace T4

structure Tel where
  Γ : Type
  H : Γ → Prop
  C : Γ → Prop

def Tel.Closed (S : Tel) : Prop := ∀ x, S.H x → S.C x

def Tel.curry (S : Tel) : Tel := ⟨S.Γ, fun _ => True, fun x => S.H x → S.C x⟩

def Tel.sentence (p : Prop) : Tel := ⟨Unit, fun _ => True, fun _ => p⟩

structure ReprInvariant (r : Tel → Tel → Prop) : Prop where
  equiv : Equivalence r
  curry : ∀ S : Tel, r S S.curry
  fold : ∀ (Γ : Type) (φ : Γ → Prop), r ⟨Γ, fun _ => True, φ⟩ (Tel.sentence (∀ x, φ x))
  ext : ∀ p q : Prop, (p ↔ q) → r (Tel.sentence p) (Tel.sentence q)

variable {r : Tel → Tel → Prop}

theorem ReprInvariant.to_sentence (hr : ReprInvariant r) (S : Tel) :
    r S (Tel.sentence S.Closed) :=
  hr.equiv.trans (hr.curry S) (hr.fold S.Γ fun x => S.H x → S.C x)

theorem ReprInvariant.collapse (hr : ReprInvariant r) {R S : Tel}
    (h : R.Closed ↔ S.Closed) : r R S :=
  hr.equiv.trans (hr.to_sentence R)
    (hr.equiv.trans (hr.ext _ _ h) (hr.equiv.symm (hr.to_sentence S)))

theorem ReprInvariant.true_collapse (hr : ReprInvariant r) {R S : Tel}
    (hR : R.Closed) (hS : S.Closed) : r R S :=
  hr.collapse ⟨fun _ => hS, fun _ => hR⟩

/-- Closed equivalence itself is representation invariant, so the bound is attained. -/
theorem closed_reprInvariant : ReprInvariant fun R S => R.Closed ↔ S.Closed where
  equiv := ⟨fun _ => Iff.rfl, Iff.symm, Iff.trans⟩
  curry _ := ⟨fun h x _ => h x, fun h x hx => h x trivial hx⟩
  fold _ _ := ⟨fun h _ _ x => h x trivial, fun h x _ => h () trivial x⟩
  ext _ _ h := ⟨fun hp u t => h.1 (hp u t), fun hq u t => h.2 (hq u t)⟩

def AlignedCond (R S : Tel) : Prop :=
  ∃ e : R.Γ ≃ S.Γ, ∀ x, (R.H x ↔ S.H (e x)) ∧ (R.H x → (R.C x ↔ S.C (e x)))

def AlignedComp (R S : Tel) : Prop :=
  ∃ e : R.Γ ≃ S.Γ, ∀ x, (R.H x ↔ S.H (e x)) ∧ (R.C x ↔ S.C (e x))

theorem AlignedComp.cond {R S : Tel} (h : AlignedComp R S) : AlignedCond R S := by
  obtain ⟨e, he⟩ := h
  exact ⟨e, fun x => ⟨(he x).1, fun _ => (he x).2⟩⟩

theorem AlignedCond.closed {R S : Tel} (h : AlignedCond R S) : R.Closed ↔ S.Closed := by
  obtain ⟨e, he⟩ := h
  constructor
  · intro hR y hy
    have hx := (he (e.symm y)).1
    rw [e.apply_symm_apply] at hx
    have := ((he (e.symm y)).2 (hx.2 hy)).1 (hR _ (hx.2 hy))
    rwa [e.apply_symm_apply] at this
  · intro hS x hx
    exact ((he x).2 hx).2 (hS _ ((he x).1.1 hx))

def boolHyp : Tel := ⟨Bool, fun b => b = true, fun _ => True⟩

theorem alignedCond_not_curry : ¬ AlignedCond boolHyp boolHyp.curry := by
  rintro ⟨e, he⟩
  have := (he false).1
  simp [boolHyp, Tel.curry] at this

theorem alignedCond_not_reprInvariant : ¬ ReprInvariant AlignedCond :=
  fun hr => alignedCond_not_curry (hr.curry boolHyp)

theorem alignedComp_not_reprInvariant : ¬ ReprInvariant AlignedComp :=
  fun hr => alignedCond_not_curry (hr.curry boolHyp).cond

end T4

#print axioms T4.ReprInvariant.collapse
#print axioms T4.closed_reprInvariant
#print axioms T4.alignedComp_not_reprInvariant
#print axioms T4.AlignedCond.closed
