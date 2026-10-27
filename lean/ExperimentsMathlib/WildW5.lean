import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Normed.Group.Continuity

/-!
# Wild W5：可微推出连续，被写成连续推出可微

绝对值在 `0` 处连续但不可微。
-/

namespace WildW5

theorem continuous_abs : Continuous (fun x : ℝ => |x|) := by
  have h : Continuous (fun x : ℝ => ‖x‖) := continuous_norm
  convert h using 1

theorem differentiable_implies_continuous (f : ℝ → ℝ) (hf : Differentiable ℝ f) :
    Continuous f :=
  hf.continuous

theorem not_continuous_implies_differentiable :
    ¬ ∀ f : ℝ → ℝ, Continuous f → Differentiable ℝ f := by
  intro h
  exact not_differentiableAt_abs_zero
    ((h (fun x : ℝ => |x|) continuous_abs).differentiableAt (x := 0))

theorem separated :
    (∀ f : ℝ → ℝ, Differentiable ℝ f → Continuous f) ∧
      ¬ ∀ f : ℝ → ℝ, Continuous f → Differentiable ℝ f :=
  ⟨differentiable_implies_continuous, not_continuous_implies_differentiable⟩

end WildW5
