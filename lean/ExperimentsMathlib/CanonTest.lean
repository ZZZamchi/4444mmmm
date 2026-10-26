import Mathlib
import ExperimentsMathlib.Canon

open Real
universe u
set_option autoImplicit false

-- pnv-test-693: same statement, one hypothesis written as an arrow
#canon_goals "693" (∀ {F V : Type u} [AddCommGroup V] [Field F] [Module F V] (v : V) (a : F), a • v = 0 → a = 0 ∨ v = 0)
  (∀ {F : Type u} [Field F] {V : Type u} [AddCommGroup V] [Module F V] (a : F) (v : V), a • v = 0 → a = 0 ∨ v = 0)

canon_prove t693 (∀ {F V : Type u} [AddCommGroup V] [Field F] [Module F V] (v : V) (a : F), a • v = 0 → a = 0 ∨ v = 0)
  (∀ {F : Type u} [Field F] {V : Type u} [AddCommGroup V] [Module F V] (a : F) (v : V), a • v = 0 → a = 0 ∨ v = 0)
  acc := by intros; exact ⟨Iff.rfl, Iff.rfl⟩

-- pnv-test-695: an abbreviation binder `f` with a defining equation
#canon_goals "695" (∀ (p : ℝ) (f : ℕ → ℝ) (hp : p > 1) (h : f = fun (k : ℕ) => (1 : ℝ) / (k * (log k) ^ p)),
    ∃ l, Filter.Tendsto f Filter.atTop (nhds l))
  (∀ (p : ℝ) (hp : 1 < p), Summable fun (k : ℕ) => 1 / (k * (log k) ^ p))

-- context drift: CommGroup vs Group
#canon_goals "drift" (∀ {G : Type u} [CommGroup G] (a b : G), a * b = b * a)
  (∀ {G : Type u} [Group G] (a b : G), a * b = b * a)

-- pnv-test-889: ¬∃ against ∀ … → False
#canon_goals "889" (¬∃ (x y : ℤ), 3 * x ^ 2 + 2 = y ^ 2)
  (∀ (m n : ℤ), 3 * m ^ 2 + 2 = n ^ 2 → False)

-- pnv-test-226: conclusion shapes differ
#canon_goals "226" (∀ {f : ℝ → ℝ}, (∀ (x y : ℝ), |f x - f y| ≤ |x - y| ^ 2) → ∃ c, f = fun _ => c)
  (∀ {f : ℝ → ℝ}, (∀ (t x : ℝ), |f t - f x| ≤ |t - x| ^ 2) → ∀ (x y : ℝ), f x = f y)

-- pnv-test-1098: ZMod n against ℤ
#canon_goals "1098" (∀ (n : ℕ) (a b c : ZMod n), a * b * c = a * (b * c))
  (∀ (n : ℕ) (a b c : ℤ), a * b % n * c % n = a * (b * c) % n)

-- a hypothesis used in the conclusion
#canon_goals "dep" (∀ (n : ℕ) (h : 0 < n), (⟨0, h⟩ : Fin n).val = 0)
  (∀ (n : ℕ) (h : 0 < n), (⟨0, h⟩ : Fin n).val = 0)
