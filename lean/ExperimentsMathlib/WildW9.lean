import Mathlib.Data.Real.Sqrt

/-!
# Wild W9：junk value 吞掉隐含条件

自然语言里的「$x/x = 1$」和「$(\sqrt{x})^2 = x$」默认 $x$ 在定义域内。
Mathlib 把除法和平方根做成全函数：`0 / 0 = 0`，负数的平方根是 `0`。
去掉定义域条件后，句子仍然能写、能编译，但为假。
-/

namespace WildW9

def divGold : Prop := ∀ x : ℝ, x ≠ 0 → x / x = 1
def divDrift : Prop := ∀ x : ℝ, x / x = 1

theorem divGold_true : divGold := fun _ hx => div_self hx

theorem divDrift_false : ¬ divDrift := by
  intro h
  have h0 := h 0
  simp at h0

def sqrtGold : Prop := ∀ x : ℝ, 0 ≤ x → Real.sqrt x ^ 2 = x
def sqrtDrift : Prop := ∀ x : ℝ, Real.sqrt x ^ 2 = x

theorem sqrtGold_true : sqrtGold := fun _ hx => Real.sq_sqrt hx

theorem sqrtDrift_false : ¬ sqrtDrift := by
  intro h
  have hneg := h (-1)
  rw [Real.sqrt_eq_zero_of_nonpos (by norm_num)] at hneg
  norm_num at hneg

theorem junk_values : (0 : ℝ) / 0 = 0 ∧ Real.sqrt (-1) = 0 :=
  ⟨div_zero 0, Real.sqrt_eq_zero_of_nonpos (by norm_num)⟩

end WildW9
