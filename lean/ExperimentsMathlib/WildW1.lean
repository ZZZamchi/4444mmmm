import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Wild W1：Heine–Cantor 结论弱化（$\Delta_C$）
-/

open Set Topology Filter

namespace WildW1

def intended (f : ℝ → ℝ) : Prop :=
  ContinuousOn f (Icc (0 : ℝ) 1) → UniformContinuousOn f (Icc (0 : ℝ) 1)

def drift (f : ℝ → ℝ) : Prop :=
  ContinuousOn f (Icc (0 : ℝ) 1)

def goldProp : Prop := ∀ f : ℝ → ℝ, intended f
def driftProp : Prop := ∀ f : ℝ → ℝ, drift f

theorem intended_holds (f : ℝ → ℝ) : intended f := by
  intro hcont
  exact IsCompact.uniformContinuousOn_of_continuous isCompact_Icc hcont

theorem goldProp_true : goldProp := intended_holds

noncomputable def step (x : ℝ) : ℝ := if x ≤ (1 / 2 : ℝ) then 0 else 1

private noncomputable def pulseSeq (n : ℕ) : ℝ := (1 / 2 : ℝ) + (1 / (n + 2 : ℝ))

private lemma pulseSeq_pos (n : ℕ) : (1 / 2 : ℝ) < pulseSeq n := by
  unfold pulseSeq
  have hn : 0 < (n + 2 : ℝ) := by exact_mod_cast (show 0 < n + 2 by omega)
  linarith [one_div_pos.mpr hn]

private lemma step_pulseSeq (n : ℕ) : step (pulseSeq n) = 1 := by
  unfold step pulseSeq
  split_ifs with h
  · exact absurd h (not_le.mpr (pulseSeq_pos n))
  · rfl

private lemma pulseSeq_tendsto : Tendsto pulseSeq atTop (nhds (1 / 2 : ℝ)) := by
  have h0 : Tendsto (fun n : ℕ => (1 / (n + 2 : ℝ))) atTop (𝓝 0) := by
    convert (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1) using 1
    ext n
    simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
    ring_nf
  have hconst : Tendsto (fun _ : ℕ => (1 / 2 : ℝ)) atTop (nhds (1 / 2 : ℝ)) := tendsto_const_nhds
  have h : Tendsto pulseSeq atTop (nhds ((1 / 2 : ℝ) + 0)) := by
    refine (hconst.add h0).congr fun n => ?_
    simp [pulseSeq]
  simpa using h

theorem step_not_continuousOn : ¬ ContinuousOn step (Icc (0 : ℝ) 1) := by
  intro h
  have hmid : (1 / 2 : ℝ) ∈ interior (Icc (0 : ℝ) 1) := by
    rw [interior_Icc]
    exact ⟨by norm_num, by norm_num⟩
  have hns : Icc (0 : ℝ) 1 ∈ 𝓝 (1 / 2 : ℝ) := mem_interior_iff_mem_nhds.mp hmid
  have hcont := h.continuousAt hns
  have hz : Tendsto (step ∘ pulseSeq) atTop (nhds 0) := by
    simpa [step] using hcont.tendsto.comp pulseSeq_tendsto
  have h1 : Tendsto (step ∘ pulseSeq) atTop (nhds 1) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [] with n
    rw [Function.comp_apply, step_pulseSeq]
  exact absurd (tendsto_nhds_unique hz h1) (by norm_num : (0 : ℝ) ≠ 1)

theorem driftProp_false : ¬ driftProp := by
  intro h
  exact step_not_continuousOn (h step)

theorem not_propositionally_equivalent : ¬ (goldProp ↔ driftProp) := by
  intro h
  exact driftProp_false (h.mp goldProp_true)

end WildW1
