import Mathlib

/-!
# T8 What single-hypothesis probes can and cannot see

For a statement `∀ x, H₁ x → H₂ x → C x` the single-hypothesis probes of §5 are, for `k = 1`,

* `implied₁ := ∀ x, H₂ x → H₁ x`,
* `idle₁    := ∀ x, H₂ x → ¬ H₁ x → C x`,

and a hypothesis is flagged when it is idle and not implied. The whole-statement probes are

* `Vacuous := ∀ x, H₁ x → H₂ x → False`,
* `Trivial := ∀ x, C x`.

Results:

* `trivial_idle`: a trivial conclusion makes every hypothesis idle, so single probes detect
  trivial conclusions as soon as one hypothesis is not implied by the other.
* `vacuous_closed`, `vacuous_iff`: a vacuous statement is true for every conclusion, and
  conversely; `trivial_closed`.
* `joint_vacuous_missed`: a jointly vacuous statement whose hypotheses are individually
  satisfiable, with the conclusion failing on each, carries no single-hypothesis flag. This is
  the gap the whole-statement probe `vacuous` closes.
* `single_flag_sound`: a flag is a real point where the statement holds without the flagged
  hypothesis.
* `implied_iff_comp`, `flag_iff`: the probe proposition of §5 for `k = 1`.
-/

namespace T8

variable {α : Type*} (H₁ H₂ C : α → Prop)

def Closed : Prop := ∀ x, H₁ x → H₂ x → C x

def Implied₁ : Prop := ∀ x, H₂ x → H₁ x
def Idle₁ : Prop := ∀ x, H₂ x → ¬ H₁ x → C x
def Implied₂ : Prop := ∀ x, H₁ x → H₂ x
def Idle₂ : Prop := ∀ x, H₁ x → ¬ H₂ x → C x

def Flag₁ : Prop := Idle₁ H₁ H₂ C ∧ ¬ Implied₁ H₁ H₂
def Flag₂ : Prop := Idle₂ H₁ H₂ C ∧ ¬ Implied₂ H₁ H₂

def Vacuous : Prop := ∀ x, H₁ x → H₂ x → False
def Trivial : Prop := ∀ x, C x

theorem trivial_idle (h : Trivial C) : Idle₁ H₁ H₂ C ∧ Idle₂ H₁ H₂ C :=
  ⟨fun x _ _ => h x, fun x _ _ => h x⟩

theorem trivial_closed (h : Trivial C) : Closed H₁ H₂ C := fun x _ _ => h x

theorem vacuous_closed (h : Vacuous H₁ H₂) : Closed H₁ H₂ C := fun x h1 h2 => (h x h1 h2).elim

theorem vacuous_iff : Vacuous H₁ H₂ ↔ ∀ C : α → Prop, Closed H₁ H₂ C :=
  ⟨fun h C => vacuous_closed H₁ H₂ C h, fun h => h fun _ => False⟩

/-- A flag on `H₁` is a point where `H₂` holds, `H₁` fails and the conclusion holds: the
statement remains true at a real point without `H₁`. -/
theorem single_flag_sound (h : Flag₁ H₁ H₂ C) : ∃ x, H₂ x ∧ ¬ H₁ x ∧ C x := by
  obtain ⟨hi, hn⟩ := h
  by_contra hall
  push_neg at hall
  exact hn fun x h2 => by
    by_contra h1
    exact hall x h2 h1 (hi x h2 h1)

/-! ## The probe proposition

`S = (H₁ ∧ H₂, C)` and `S∖₁ = (H₂, C)`, written out with the component and conditional
relations of T6. -/

/-- `implied₁` holds iff `S` and `S∖₁` are component-equivalent. -/
theorem implied_iff_comp :
    Implied₁ H₁ H₂ ↔ ∀ x, ((H₁ x ∧ H₂ x) ↔ H₂ x) ∧ (C x ↔ C x) :=
  ⟨fun h x => ⟨⟨And.right, fun h2 => ⟨h x h2, h2⟩⟩, Iff.rfl⟩, fun h x h2 => ((h x).1.2 h2).1⟩

/-- For a true `S`, a flag on `H₁` holds iff `S∖₁` is true and not conditionally equivalent to
`S`: the hypothesis is decorative. -/
theorem flag_iff (hS : Closed H₁ H₂ C) :
    Flag₁ H₁ H₂ C ↔ (∀ x, H₂ x → C x) ∧
      ¬ ∀ x, ((H₁ x ∧ H₂ x) ↔ H₂ x) ∧ ((H₁ x ∧ H₂ x) → (C x ↔ C x)) := by
  have hc : (∀ x, ((H₁ x ∧ H₂ x) ↔ H₂ x) ∧ ((H₁ x ∧ H₂ x) → (C x ↔ C x))) ↔ Implied₁ H₁ H₂ :=
    ⟨fun h x h2 => ((h x).1.2 h2).1,
     fun h x => ⟨⟨And.right, fun h2 => ⟨h x h2, h2⟩⟩, fun _ => Iff.rfl⟩⟩
  rw [hc]
  refine ⟨fun ⟨hi, hn⟩ => ⟨fun x h2 => ?_, hn⟩, fun ⟨hd, hn⟩ => ⟨fun x h2 _ => hd x h2, hn⟩⟩
  by_cases h1 : H₁ x
  · exact hS x h1 h2
  · exact hi x h2 h1

/-! ## The gap: joint vacuity -/

def P₁ : ℤ → Prop := fun x => 0 < x
def P₂ : ℤ → Prop := fun x => x < 0
def Q : ℤ → Prop := fun x => x = 1

theorem ex_vacuous : Vacuous P₁ P₂ := fun x h1 h2 => by
  simp only [P₁, P₂] at h1 h2
  omega

theorem ex_no_flag : ¬ Flag₁ P₁ P₂ Q ∧ ¬ Flag₂ P₁ P₂ Q := by
  constructor
  · rintro ⟨hi, -⟩
    have := hi (-1) (by simp [P₂]) (by simp [P₁])
    simp [Q] at this
  · rintro ⟨hi, -⟩
    have := hi 2 (by simp [P₁]) (by simp [P₂])
    simp [Q] at this

theorem ex_not_implied : ¬ Implied₁ P₁ P₂ ∧ ¬ Implied₂ P₁ P₂ :=
  ⟨fun h => by have := h (-1) (by simp [P₂]); simp [P₁] at this,
   fun h => by have := h 1 (by simp [P₁]); simp [P₂] at this⟩

/-- A jointly vacuous statement, each hypothesis satisfiable on its own, no single-hypothesis
flag. -/
theorem joint_vacuous_missed :
    Vacuous P₁ P₂ ∧ (∃ x, P₁ x) ∧ (∃ x, P₂ x) ∧ ¬ Flag₁ P₁ P₂ Q ∧ ¬ Flag₂ P₁ P₂ Q :=
  ⟨ex_vacuous, ⟨1, by simp [P₁]⟩, ⟨-1, by simp [P₂]⟩, ex_no_flag.1, ex_no_flag.2⟩

/-! ## Correspondence with vacuity detection

A statement `∀ x, (∀ i, H i x) → C x` with `m` hypotheses. In the sense of Kupferman and Vardi
it is vacuous in a subformula if replacing that subformula by an arbitrary one keeps it true.
The probes are exactly these tests: vacuity in `H k` is `idle k`, vacuity in `C` is
`vacuous` (`vacuous_iff` above, here `vacuousIn_concl_iff`), and vacuity in all hypotheses at
once is `trivial`. -/

section KV

variable {m : ℕ} (H : Fin m → α → Prop) (C : α → Prop)

def HoldsM : Prop := ∀ x, (∀ i, H i x) → C x

def VacuousInHyp (k : Fin m) : Prop := ∀ ψ : α → Prop, HoldsM (Function.update H k ψ) C

def VacuousInConcl : Prop := ∀ ψ : α → Prop, HoldsM H ψ

def VacuousInAllHyps : Prop := ∀ G : Fin m → α → Prop, HoldsM G C

def IdleM (k : Fin m) : Prop := ∀ x, (∀ i, i ≠ k → H i x) → ¬ H k x → C x

theorem vacuousIn_hyp_iff_drop (k : Fin m) :
    VacuousInHyp H C k ↔ HoldsM (Function.update H k fun _ => True) C := by
  refine ⟨fun h => h _, fun h ψ x hx => h x fun i => ?_⟩
  by_cases hi : i = k
  · subst hi; simp
  · have := hx i; rwa [Function.update_of_ne hi] at this ⊢

/-- For a true statement, vacuity in `H k` is exactly the probe `idle k`. -/
theorem vacuousIn_hyp_iff_idle (hS : HoldsM H C) (k : Fin m) :
    VacuousInHyp H C k ↔ IdleM H C k := by
  rw [vacuousIn_hyp_iff_drop]
  constructor
  · intro h x hx _
    refine h x fun i => ?_
    by_cases hi : i = k
    · subst hi; simp
    · rw [Function.update_of_ne hi]; exact hx i hi
  · intro h x hx
    have hx' : ∀ i, i ≠ k → H i x := fun i hi => by
      have := hx i; rwa [Function.update_of_ne hi] at this
    by_cases hk : H k x
    · exact hS x fun i => if hi : i = k then hi ▸ hk else hx' i hi
    · exact h x hx' hk

theorem vacuousIn_concl_iff : VacuousInConcl H ↔ ∀ x, ¬ ∀ i, H i x :=
  ⟨fun h x hx => h (fun _ => False) x hx, fun h _ x hx => (h x hx).elim⟩

theorem vacuousIn_allHyps_iff : VacuousInAllHyps (α := α) (m := m) C ↔ ∀ x, C x :=
  ⟨fun h x => h (fun _ _ => True) x fun _ => trivial, fun h _ x _ => h x⟩

end KV

end T8

#print axioms T8.single_flag_sound
#print axioms T8.implied_iff_comp
#print axioms T8.flag_iff
#print axioms T8.vacuous_iff
#print axioms T8.trivial_idle
#print axioms T8.joint_vacuous_missed
#print axioms T8.vacuousIn_hyp_iff_idle
#print axioms T8.vacuousIn_concl_iff
#print axioms T8.vacuousIn_allHyps_iff
