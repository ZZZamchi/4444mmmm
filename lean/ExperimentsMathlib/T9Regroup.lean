import Mathlib

/-!
# T9 Dependence on the hypothesis/conclusion split

Over an aligned context, a *regrouping* moves a Prop `P` between the hypotheses and the
conclusion: `(H ∧ P, C)` versus `(H, P → C)`. An equivalence relation that accepts
component-equivalent pairs and is invariant under regrouping contains pointwise implication
(`regroup_forces_pointImp`); with soundness and restriction it is exactly pointwise implication
(`regroup_eq_pointImp`), so it identifies any two true statements over the context.

Regrouping preserves the pointwise claim, so a reject that is not pointwise-equivalent survives
every regrouping of either side (`robust_reject`), while a vacuity-only reject becomes an accept
once both sides are fully curried (`vacuity_only_curry_accept`). Since two true statements are
pointwise equivalent, a reject outside pointwise implication certifies that one side is false
(`not_closed_of_not_pointImp`), and with a direction it says which (`not_closed_of_rs`).
-/

namespace T9

structure Stmt (α : Type*) where
  H : α → Prop
  C : α → Prop

variable {α : Type*}

def Stmt.Closed (S : Stmt α) : Prop := ∀ x, S.H x → S.C x

def Stmt.restrict (S : Stmt α) (P : α → Prop) : Stmt α := ⟨fun x => S.H x ∧ P x, S.C⟩

def Stmt.curry (S : Stmt α) : Stmt α := ⟨fun _ => True, fun x => S.H x → S.C x⟩

def PointImp (R S : Stmt α) : Prop := ∀ x, (R.H x → R.C x) ↔ (S.H x → S.C x)

def CompEquiv (R S : Stmt α) : Prop := ∀ x, (R.H x ↔ S.H x) ∧ (R.C x ↔ S.C x)

def Sound (r : Stmt α → Stmt α → Prop) : Prop := ∀ R S, r R S → (R.Closed ↔ S.Closed)

def Restrict (r : Stmt α → Stmt α → Prop) : Prop :=
  ∀ R S (P : α → Prop), r R S → r (R.restrict P) (S.restrict P)

/-- Moving `P` from the hypotheses to the conclusion does not change the verdict. -/
def RegroupInvariant (r : Stmt α → Stmt α → Prop) : Prop :=
  ∀ H P C : α → Prop, r ⟨fun x => H x ∧ P x, C⟩ ⟨H, fun x => P x → C x⟩

theorem curry_related {r : Stmt α → Stmt α → Prop} (he : Equivalence r)
    (hc : ∀ R S, CompEquiv R S → r R S) (hg : RegroupInvariant r) (S : Stmt α) :
    r S S.curry :=
  he.trans (hc _ ⟨fun x => True ∧ S.H x, S.C⟩ fun _ => ⟨⟨fun h => ⟨trivial, h⟩, And.right⟩, Iff.rfl⟩)
    (hg (fun _ => True) S.H S.C)

theorem regroup_forces_pointImp {r : Stmt α → Stmt α → Prop} (he : Equivalence r)
    (hc : ∀ R S, CompEquiv R S → r R S) (hg : RegroupInvariant r) {R S : Stmt α}
    (h : PointImp R S) : r R S :=
  he.trans (curry_related he hc hg R)
    (he.trans (hc R.curry S.curry fun x => ⟨Iff.rfl, h x⟩) (he.symm (curry_related he hc hg S)))

theorem le_pointImp {r : Stmt α → Stmt α → Prop} (hs : Sound r) (hr : Restrict r) {R S : Stmt α}
    (h : r R S) : PointImp R S := fun x => by
  have := hs _ _ (hr R S (· = x) h)
  exact ⟨fun hR hx => this.1 (fun y ⟨hy, e⟩ => e ▸ hR (e ▸ hy)) x ⟨hx, rfl⟩,
    fun hS hx => this.2 (fun y ⟨hy, e⟩ => e ▸ hS (e ▸ hy)) x ⟨hx, rfl⟩⟩

theorem regroup_eq_pointImp {r : Stmt α → Stmt α → Prop} (he : Equivalence r)
    (hc : ∀ R S, CompEquiv R S → r R S) (hg : RegroupInvariant r) (hs : Sound r)
    (hr : Restrict r) {R S : Stmt α} : r R S ↔ PointImp R S :=
  ⟨le_pointImp hs hr, regroup_forces_pointImp he hc hg⟩

theorem regroup_true_collapse {r : Stmt α → Stmt α → Prop} (he : Equivalence r)
    (hc : ∀ R S, CompEquiv R S → r R S) (hg : RegroupInvariant r) {R S : Stmt α}
    (hR : R.Closed) (hS : S.Closed) : r R S :=
  regroup_forces_pointImp he hc hg fun x => ⟨fun _ => hS x, fun _ => hR x⟩

/-- Pointwise implication itself is regroup invariant, so the bound is attained. -/
theorem pointImp_regroupInvariant : RegroupInvariant (PointImp (α := α)) := fun _ _ _ _ =>
  ⟨fun h hx p => h ⟨hx, p⟩, fun h ⟨hx, p⟩ => h hx p⟩

theorem pointImp_equivalence : Equivalence (PointImp (α := α)) :=
  ⟨fun _ _ => Iff.rfl, fun h x => (h x).symm, fun h k x => (h x).trans (k x)⟩

theorem compEquiv_pointImp {R S : Stmt α} (h : CompEquiv R S) : PointImp R S := fun x =>
  ⟨fun hR hx => (h x).2.1 (hR ((h x).1.2 hx)), fun hS hx => (h x).2.2 (hS ((h x).1.1 hx))⟩

/-- A reject outside pointwise implication survives any re-presentation that keeps the pointwise
claims, in particular any sequence of regroupings on either side. -/
theorem robust_reject {R R' S S' : Stmt α} (hR : PointImp R R') (hS : PointImp S S')
    (h : ¬ PointImp R S) : ¬ CompEquiv R' S' := fun hc =>
  h (pointImp_equivalence.trans hR
    (pointImp_equivalence.trans (compEquiv_pointImp hc) (pointImp_equivalence.symm hS)))

/-- A vacuity-only reject turns into an accept once both sides are fully curried. -/
theorem vacuity_only_curry_accept {R S : Stmt α} (h : PointImp R S) :
    CompEquiv R.curry S.curry := fun x => ⟨Iff.rfl, h x⟩

/-- Two true statements are pointwise equivalent, so a reject outside pointwise implication
certifies that one of them is false. -/
theorem not_closed_of_not_pointImp {R S : Stmt α} (h : ¬ PointImp R S) : ¬ R.Closed ∨ ¬ S.Closed := by
  by_contra hc
  push_neg at hc
  exact h fun x => ⟨fun _ => hc.2 x, fun _ => hc.1 x⟩

/-- With the direction `rs` (whatever `R` claims at a point, `S` claims too), the false one is `R`. -/
theorem not_closed_of_rs {R S : Stmt α} (hrs : ∀ x, (R.H x → R.C x) → (S.H x → S.C x))
    (h : ¬ PointImp R S) : ¬ R.Closed :=
  fun hR => h fun x => ⟨fun _ => hrs x (hR x), fun _ => hR x⟩

/-! ### Certificate semantics

`clR`, `clS` are the elaborated statements and `TR`, `TS` the telescopes exhibited by the
canonicalizer; `split_r : clR ↔ TR.Closed` and `split_s` are the regrouping certificates. The
conclusions below hold whatever code produced `TR` and `TS`. -/

def CondEquiv (R S : Stmt α) : Prop := ∀ x, (R.H x ↔ S.H x) ∧ (R.H x → (R.C x ↔ S.C x))

theorem condEquiv_closed {R S : Stmt α} (h : CondEquiv R S) : R.Closed ↔ S.Closed :=
  ⟨fun hR x hx => ((h x).2 ((h x).1.2 hx)).1 (hR x ((h x).1.2 hx)),
   fun hS x hx => ((h x).2 hx).2 (hS x ((h x).1.1 hx))⟩

theorem compEquiv_cond {R S : Stmt α} (h : CompEquiv R S) : CondEquiv R S :=
  fun x => ⟨(h x).1, fun _ => (h x).2⟩

/-- An accept or residual certificate decides the original statements. -/
theorem cert_accept {clR clS : Prop} {TR TS : Stmt α} (split_r : clR ↔ TR.Closed)
    (split_s : clS ↔ TS.Closed) (h : CompEquiv TR TS) : clR ↔ clS :=
  split_r.trans ((condEquiv_closed (compEquiv_cond h)).trans split_s.symm)

/-- An off-domain certificate also decides the original statements. -/
theorem cert_offDomain {clR clS : Prop} {TR TS : Stmt α} (split_r : clR ↔ TR.Closed)
    (split_s : clS ↔ TS.Closed) (h : CondEquiv TR TS) : clR ↔ clS :=
  split_r.trans ((condEquiv_closed h).trans split_s.symm)

/-- A closed refutation with both regrouping certificates refutes conditional equivalence of the
exhibited telescopes. -/
theorem cert_closed_refute {clR clS : Prop} {TR TS : Stmt α} (split_r : clR ↔ TR.Closed)
    (split_s : clS ↔ TS.Closed) (h : ¬ (clR ↔ clS)) : ¬ CondEquiv TR TS :=
  fun hc => h (cert_offDomain split_r split_s hc)

/-- A robust reject with the direction `rs` refutes the original candidate statement `clR`. -/
theorem cert_robust_reject {clR : Prop} {TR TS : Stmt α} (split_r : clR ↔ TR.Closed)
    (hrs : ∀ x, (TR.H x → TR.C x) → (TS.H x → TS.C x)) (h : ¬ PointImp TR TS) : ¬ clR :=
  fun hc => not_closed_of_rs hrs h (split_r.1 hc)

end T9

#print axioms T9.regroup_eq_pointImp
#print axioms T9.regroup_true_collapse
#print axioms T9.pointImp_regroupInvariant
#print axioms T9.robust_reject
#print axioms T9.vacuity_only_curry_accept
#print axioms T9.not_closed_of_not_pointImp
#print axioms T9.not_closed_of_rs
#print axioms T9.cert_accept
#print axioms T9.cert_closed_refute
#print axioms T9.cert_robust_reject
