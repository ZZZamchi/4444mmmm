import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.Compact

/-!
# Wild W7：紧区间上的极值，被写成开区间

连续函数在 `[0,1]` 上取到最大值。
在 `(0,1)` 上，恒等函数没有最大值。
-/

open Set

namespace WildW7

def gold (f : ℝ → ℝ) : Prop :=
  ContinuousOn f (Icc (0 : ℝ) 1) →
    ∃ x ∈ Icc (0 : ℝ) 1, IsMaxOn f (Icc (0 : ℝ) 1) x

def drift (f : ℝ → ℝ) : Prop :=
  ContinuousOn f (Ioo (0 : ℝ) 1) →
    ∃ x ∈ Ioo (0 : ℝ) 1, IsMaxOn f (Ioo (0 : ℝ) 1) x

theorem gold_holds (f : ℝ → ℝ) : gold f := by
  intro hf
  exact isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr (by norm_num : (0 : ℝ) ≤ 1)) hf

theorem no_max_id : ¬ ∃ x ∈ Ioo (0 : ℝ) 1, IsMaxOn id (Ioo (0 : ℝ) 1) x := by
  intro ⟨x, hx, hmax⟩
  obtain ⟨z, hxz, hz1⟩ := exists_between hx.2
  have hz : z ∈ Ioo (0 : ℝ) 1 := ⟨lt_trans hx.1 hxz, hz1⟩
  exact lt_irrefl x (lt_of_lt_of_le hxz (hmax hz))

theorem not_drift_id : ¬ drift id := by
  intro h
  exact no_max_id (h continuous_id.continuousOn)

theorem separated : gold id ∧ ¬ drift id :=
  ⟨gold_holds id, not_drift_id⟩

end WildW7
