import Mathlib
import ExperimentsMathlib.CanonV2

open Set

#canon2_goals "neg" (∀ {X : Type} [TopologicalSpace X] {A C : Set X} (hc : IsConnected C) (hCA : C ∩ A ≠ ∅) (hCXA : C ∩ Aᶜ ≠ ∅), C ∩ (frontier A) ≠ ∅) (∀ {X : Type} [TopologicalSpace X] {A : Set X} {C : Set X} (hA : IsConnected C) (hAC : C ∩ A ≠ ∅) (hAC' : C ∩ closure Aᶜ ≠ ∅), C ∩ frontier A ≠ ∅)

#canon2_goals "hoist" (∀ {G : Type} [Group G] {p : ℕ} (hp : Nat.Prime p) (P : Subgroup G), P.Normal → P = P) (∀ {G : Type} [Group G] {p : ℕ} (Q : Sylow p G) (hp : Nat.Prime p), (Q : Subgroup G).Normal → True)

#canon2_goals "bot" (∀ {G : Type} [Group G] [Fintype G] (hG : Fintype.card G = 224), IsSimpleGroup G → false) (∀ {G : Type} [Group G] [Fintype G] (hG : Fintype.card G = 224), ¬ IsSimpleGroup G)

#canon2_goals "negex" (¬ ∃ n : ℕ, n + 1 = 0) (∀ n : ℕ, n + 1 ≠ 0)

canon2_prove t_neg_split (¬ ∃ n : ℕ, n + 1 = 0) (∀ n : ℕ, n + 1 ≠ 0) acc := by
  intro n; exact ⟨Iff.rfl, Iff.rfl⟩
