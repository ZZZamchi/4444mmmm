import Mathlib.Algebra.Field.Rat
import Mathlib.Data.Nat.Basic

/-!
# Wild W4：乘法逆元的载体（$\Delta_T$）

同一句话「每个非零元都有乘法逆」在 $\mathbb{N}$ 上为假，在 $\mathbb{Q}$ 上为真。
-/

namespace WildW4

def onNat : Prop := ∀ n : ℕ, n ≠ 0 → ∃ m : ℕ, n * m = 1

def onRat : Prop := ∀ q : ℚ, q ≠ 0 → ∃ r : ℚ, q * r = 1

theorem onNat_false : ¬ onNat := by
  intro h
  obtain ⟨m, hm⟩ := h 2 (by decide)
  match m with
  | 0 => cases hm
  | 1 => cases hm
  | m + 2 =>
      have hge : 4 ≤ 2 * (m + 2) := by
        have htwo : 2 ≤ m + 2 := Nat.le_add_left 2 m
        have hmul : 2 * 2 ≤ 2 * (m + 2) := Nat.mul_le_mul_left 2 htwo
        exact hmul
      exact absurd (show 4 ≤ 1 by rw [← hm]; exact hge) (by decide)

theorem onRat_true : onRat := by
  intro q hq
  exact ⟨q⁻¹, mul_inv_cancel₀ hq⟩

theorem not_propositionally_equivalent : ¬ (onNat ↔ onRat) :=
  fun h => onNat_false (h.mpr onRat_true)

end WildW4
