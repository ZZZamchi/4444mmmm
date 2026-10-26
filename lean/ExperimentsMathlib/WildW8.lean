import Mathlib.Algebra.BigOperators.Intervals

/-!
# Wild W8：求和下标差一

「$0+1+\cdots+n = n(n+1)/2$」写成 `range (n + 1)` 时成立。
写成 `range n` 时漏掉最后一项，`n = 1` 时左边是 `0`，右边是 `1`。
-/

open Finset

namespace WildW8

def gold : Prop := ∀ n : ℕ, ∑ i ∈ range (n + 1), i = n * (n + 1) / 2

def drift : Prop := ∀ n : ℕ, ∑ i ∈ range n, i = n * (n + 1) / 2

theorem gold_true : gold := by
  intro n
  rw [sum_range_id, Nat.add_sub_cancel, Nat.mul_comm]

theorem drift_false : ¬ drift := by
  intro h
  have h1 := h 1
  simp at h1

theorem not_propositionally_equivalent : ¬ (gold ↔ drift) :=
  fun h => drift_false (h.mp gold_true)

end WildW8
