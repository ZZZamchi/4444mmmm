import Mathlib.Data.Real.Basic

/-!
# Wild W2：ε-δ 量词颠倒（$\Delta_\forall$）

自然语言：对任意 $\varepsilon>0$ 存在 $\delta>0$。
漂移读法：存在一个 $\delta>0$ 对所有 $\varepsilon>0$ 都成立。
在恒等函数上，前者成立，后者不成立。
-/

namespace WildW2

def goldEpsDelta (f : ℝ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ x y : ℝ, 0 ≤ x → x ≤ 1 → 0 ≤ y → y ≤ 1 → |x - y| < δ → |f x - f y| < ε

def driftSwap (f : ℝ → ℝ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε →
    ∀ x y : ℝ, 0 ≤ x → x ≤ 1 → 0 ≤ y → y ≤ 1 → |x - y| < δ → |f x - f y| < ε

theorem gold_id : goldEpsDelta id := by
  intro ε hε
  refine ⟨ε, hε, ?_⟩
  intro x y _ _ _ _ hdist
  simpa using hdist

theorem not_drift_id : ¬ driftSwap id := by
  rintro ⟨δ, hδ, h⟩
  let ε : ℝ := min δ 1 / 2
  have hε : 0 < ε := by
    have hmin : 0 < min δ (1 : ℝ) := lt_min hδ zero_lt_one
    exact div_pos hmin two_pos
  have hy1 : ε ≤ 1 := by
    have hmin : min δ (1 : ℝ) ≤ 1 := min_le_right _ _
    have hhalf : min δ 1 / 2 ≤ 1 / 2 :=
      div_le_div_of_nonneg_right hmin (by norm_num : (0 : ℝ) ≤ 2)
    have h12 : (1 : ℝ) / 2 ≤ 1 := half_le_self (by norm_num)
    exact le_trans (le_of_eq (by rfl : ε = min δ 1 / 2)) (le_trans hhalf h12)
  have hdist : |ε - 0| < δ := by
    have hnn : 0 ≤ ε := le_of_lt hε
    rw [sub_zero, abs_of_nonneg hnn]
    have hle : min δ (1 : ℝ) / 2 ≤ δ / 2 :=
      div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num : (0 : ℝ) ≤ 2)
    exact lt_of_le_of_lt (le_trans (le_of_eq (by rfl : ε = min δ 1 / 2)) hle) (half_lt_self hδ)
  have hbad : |id ε - id 0| < ε :=
    h ε hε ε 0 (le_of_lt hε) hy1 (by norm_num) (by norm_num) hdist
  simp only [id_eq, sub_zero, abs_of_nonneg (le_of_lt hε)] at hbad
  exact lt_irrefl ε hbad

theorem gold_not_swap : goldEpsDelta id ∧ ¬ driftSwap id :=
  ⟨gold_id, not_drift_id⟩

theorem not_propositionally_equivalent : ¬ (goldEpsDelta id ↔ driftSwap id) := by
  intro h
  exact not_drift_id (h.mp gold_id)

end WildW2
