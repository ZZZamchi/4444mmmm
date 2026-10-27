import Mathlib
import ExperimentsMathlib.CanonV2Ext

#canon2x_goals "pnat" "subtype" (∀ n : ℕ+, (n : ℕ) ^ 2 ≥ n) (∀ n : ℕ, 0 < n → n ^ 2 ≥ n)

#canon2x_goals "elem" "subtype" (∀ (s : Set ℝ) (x : s), (x : ℝ) ∈ s) (∀ (s : Set ℝ) (x : ℝ), x ∈ s → x ∈ s)

#canon2x_goals "dec" "classdec"
  (∀ (G : Type) [Group G] [DecidableEq G] [Fintype G], Fintype.card G ≥ 1)
  (∀ (G : Type) [Group G] [Fintype G], Fintype.card G ≥ 1)

#canon2x_goals "unused" "dropunused" (∀ (m : ℕ) (x : ℝ), x ^ 2 ≥ 0) (∀ x : ℝ, x ^ 2 ≥ 0)

universe u in
#canon2x_goals "univ" "univ0" (∀ (G : Type u) [Group G] [Fintype G], Fintype.card G ≥ 1)
  (∀ (G : Type) [Group G] [Fintype G], Fintype.card G ≥ 1)

canon2x_prove "subtype" pnat_split ((∀ n : ℕ+, (n : ℕ) ^ 2 ≥ n)) ((∀ n : ℕ, 0 < n → n ^ 2 ≥ n)) split_r := by
  constructor
  · intro h n hn; exact h ⟨n, hn⟩
  · intro h n; exact h n n.2

canon2x_prove "classdec" dec_split
  ((∀ (G : Type) [Group G] [DecidableEq G] [Fintype G], Fintype.card G ≥ 1))
  ((∀ (G : Type) [Group G] [Fintype G], Fintype.card G ≥ 1)) split_r := by
  constructor
  · intro h G _ _ _
    classical
    exact h G
  · intro h G _ _ _
    exact h G trivial

canon2x_prove "dropunused" unused_split ((∀ (m : ℕ) (x : ℝ), x ^ 2 ≥ 0)) ((∀ x : ℝ, x ^ 2 ≥ 0)) split_r := by
  simp only [forall_const]

#canon2x_goals "exhyp" "exhyp"
  (∀ (x : ℕ → ℝ), (∃ n, x n = 0) → ∃ c, c ≠ 0 ∧ x c = x 0)
  (∀ (x : ℕ → ℝ) (n : ℕ), x n = 0 → ∃ c, c ≠ 0 ∧ x c = x 0)

#canon2x_goals "nonempty" "nonempty"
  (∀ (G : Type) [Group G] (s : G ≃* G), (∀ g, s g = g ↔ g = 1) → ∀ a b : G, a * b = b * a)
  (∀ (G : Type) [Group G] [Fintype G] (s : G ≃* G), (∀ g, s g = g ↔ g = 1) → ∀ a b : G, a * b = b * a)

#canon2x_goals "finite" "nonempty"
  (∀ (G : Type) [Group G] [Finite G] (a : G), ∃ n : ℕ, 0 < n ∧ a ^ n = 1)
  (∀ (G : Type) [Group G] [Fintype G] (a : G), ∃ n : ℕ, 0 < n ∧ a ^ n = 1)
