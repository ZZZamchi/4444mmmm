import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.Compact

/-!
# Wild W6：紧集的连续像，被写成整个定义域的连续像

`[0,1]` 的连续像是紧的。`ℝ` 不是紧的，所以恒等映射的值域不是紧的。
-/

open Set

namespace WildW6

theorem gold (f : ℝ → ℝ) (hf : Continuous f) : IsCompact (f '' Icc (0 : ℝ) 1) :=
  isCompact_Icc.image hf

theorem not_drift : ¬ ∀ f : ℝ → ℝ, Continuous f → IsCompact (range f) := by
  intro h
  have hc : IsCompact (range (id : ℝ → ℝ)) := h id continuous_id
  rw [range_id] at hc
  have hnot : ¬ CompactSpace ℝ :=
    not_compactSpace_iff.mpr (inferInstance : NoncompactSpace ℝ)
  exact hnot (isCompact_univ_iff.mp hc)

theorem separated :
    (∀ f : ℝ → ℝ, Continuous f → IsCompact (f '' Icc (0 : ℝ) 1)) ∧
      ¬ ∀ f : ℝ → ℝ, Continuous f → IsCompact (range f) :=
  ⟨gold, not_drift⟩

end WildW6
