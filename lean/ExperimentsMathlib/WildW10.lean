import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt

/-!
# Wild W10：junk value 目录

每个运算给出三条：junk 等式、带定义域条件的句子为真、去掉条件后为假。
`data/implicit_obligations.json` 里的定理名都指向这里。
-/

namespace WildW10

theorem inv_junk : (0 : ℝ)⁻¹ = 0 := inv_zero

theorem inv_gold : ∀ x : ℝ, x ≠ 0 → x * x⁻¹ = 1 := fun _ hx => mul_inv_cancel₀ hx

theorem inv_drift_false : ¬ ∀ x : ℝ, x * x⁻¹ = 1 := by
  intro h
  have h0 := h 0
  simp at h0

theorem log_junk : Real.log 0 = 0 := Real.log_zero

theorem log_gold : ∀ x : ℝ, 0 < x → Real.exp (Real.log x) = x := fun _ hx => Real.exp_log hx

theorem log_drift_false : ¬ ∀ x : ℝ, Real.exp (Real.log x) = x := by
  intro h
  have h0 := h 0
  rw [Real.log_zero, Real.exp_zero] at h0
  norm_num at h0

theorem toNat_junk : Int.toNat (-1) = 0 := rfl

theorem toNat_gold : ∀ z : ℤ, 0 ≤ z → (Int.toNat z : ℤ) = z := fun _ hz => Int.toNat_of_nonneg hz

theorem toNat_drift_false : ¬ ∀ z : ℤ, (Int.toNat z : ℤ) = z := by
  intro h
  have h1 := h (-1)
  norm_num at h1

theorem pred_junk : Nat.pred 0 = 0 := rfl

theorem pred_gold : ∀ n : ℕ, 0 < n → Nat.pred n + 1 = n := fun _ hn => Nat.succ_pred_eq_of_pos hn

theorem pred_drift_false : ¬ ∀ n : ℕ, Nat.pred n + 1 = n := by
  intro h
  have h0 := h 0
  cases h0

end WildW10
