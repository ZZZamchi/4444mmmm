import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.IntermediateValue

/-!
# Wild W3：介值定理丢掉连续性（组合：假设遗漏）

`gold` 保留 `ContinuousOn`。`drift` 只保留端点变号。
阶跃函数 `jump` 端点变号且在 `[0,1]` 上没有零点，所以 `drift` 失败。
`gold` 是蕴涵，对 `jump` 仍然成立。
-/

open Set

namespace WildW3

def gold (f : ℝ → ℝ) : Prop :=
  ContinuousOn f (Icc (0 : ℝ) 1) →
    f 0 < 0 → 0 < f 1 → ∃ x, x ∈ Icc (0 : ℝ) 1 ∧ f x = 0

def drift (f : ℝ → ℝ) : Prop :=
  f 0 < 0 → 0 < f 1 → ∃ x, x ∈ Icc (0 : ℝ) 1 ∧ f x = 0

theorem gold_holds (f : ℝ → ℝ) : gold f := by
  intro hcont hf0 hf1
  have hmem : (0 : ℝ) ∈ Icc (f 0) (f 1) := ⟨le_of_lt hf0, le_of_lt hf1⟩
  obtain ⟨x, hx, hfx⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hcont hmem
  exact ⟨x, hx, hfx⟩

noncomputable def jump (x : ℝ) : ℝ :=
  if x < (1 / 2 : ℝ) then -1 else 1

theorem jump_ne_zero (x : ℝ) : jump x ≠ 0 := by
  unfold jump
  split_ifs <;> norm_num

theorem jump_zero : jump 0 = -1 := by
  unfold jump
  rw [if_pos (by norm_num : (0 : ℝ) < 1 / 2)]

theorem jump_one : jump 1 = 1 := by
  unfold jump
  rw [if_neg (by norm_num : ¬ ((1 : ℝ) < 1 / 2))]

theorem not_drift_jump : ¬ drift jump := by
  intro h
  have h0 : jump 0 < 0 := by rw [jump_zero]; norm_num
  have h1 : 0 < jump 1 := by rw [jump_one]; norm_num
  rcases h h0 h1 with ⟨x, _, hfx⟩
  exact jump_ne_zero x hfx

theorem separated : gold jump ∧ ¬ drift jump :=
  ⟨gold_holds jump, not_drift_jump⟩

theorem not_propositionally_equivalent : ¬ (gold jump ↔ drift jump) := by
  intro h
  exact not_drift_jump (h.mp (gold_holds jump))

end WildW3
