import Mathlib

/-!
Kernel certificates for reference-statement errors found by the hypothesis probe (G3) on
miniF2F (DeepSeek-Prover-V1.5 Lean 4 port) and PutnamBench. Each theorem keeps the benchmark's
hypotheses verbatim and derives `False` (inconsistent hypotheses) or refutes the statement.
-/

namespace BenchErrors

/-- miniF2F `aime_1996_p5`: the cubic is strictly increasing, so it has no two distinct real
roots and the hypotheses are inconsistent. -/
theorem aime_1996_p5_vacuous (a b c r s t : ℝ) (f g : ℝ → ℝ)
    (h₀ : ∀ x, f x = x ^ 3 + 3 * x ^ 2 + 4 * x - 11) (_h₁ : ∀ x, g x = x ^ 3 + r * x ^ 2 + s * x + t)
    (h₂ : f a = 0) (h₃ : f b = 0) (_h₄ : f c = 0) (_h₅ : g (a + b) = 0) (_h₆ : g (b + c) = 0)
    (_h₇ : g (c + a) = 0) (h₈ : List.Pairwise (· ≠ ·) [a, b, c]) : False := by
  rw [h₀] at h₂ h₃
  have hab : a ≠ b := by simp at h₈; exact h₈.1.1
  have hfac : (a - b) * ((a + 1) ^ 2 + (a + 1) * (b + 1) + (b + 1) ^ 2 + 1) = 0 := by
    linear_combination h₂ - h₃
  rcases mul_eq_zero.1 hfac with h | h
  · exact hab (sub_eq_zero.1 h)
  · nlinarith [sq_nonneg (a + b + 2), sq_nonneg (a - b)]

/-- miniF2F `amc12a_2003_p25`: `Real.sqrt` is total, so `{x | 0 ≤ f x}` is all of `ℝ` while
`f` only takes nonnegative values; `h₂` never holds. -/
theorem amc12a_2003_p25_vacuous (a b : ℝ) (f : ℝ → ℝ) (_h₀ : 0 < b)
    (h₁ : ∀ x, f x = Real.sqrt (a * x ^ 2 + b * x)) (h₂ : { x | 0 ≤ f x } = f '' { x | 0 ≤ f x }) :
    False := by
  have hm : (-1 : ℝ) ∈ { x | 0 ≤ f x } := by
    simp only [Set.mem_setOf_eq, h₁]; exact Real.sqrt_nonneg _
  rw [h₂] at hm
  obtain ⟨y, _, hy⟩ := hm
  have := Real.sqrt_nonneg (a * y ^ 2 + b * y)
  rw [← h₁, hy] at this
  linarith

/-- miniF2F `amc12a_2020_p13`: the exponents `1 / c`, `1 / b`, `1 / a`, `1 / 36` are natural-number
divisions, all equal to `0`, so `h₂` reads `1 = 1` and the statement is false. -/
theorem amc12a_2020_p13_false :
    ¬ ∀ (a b c : ℕ) (n : NNReal) (_h₀ : n ≠ 1) (_h₁ : 1 < a ∧ 1 < b ∧ 1 < c)
      (_h₂ : (n * (n * n ^ (1 / c)) ^ (1 / b)) ^ (1 / a) = (n ^ 25) ^ (1 / 36)), b = 3 := by
  intro h
  have := h 2 2 2 2 (by norm_num) (by norm_num) (by norm_num)
  omega

/-- miniF2F-v2s `amc12a_2020_p13`: v2 moves `n` under a binder but keeps the natural-number
exponents, so `h₁` is still trivial and the statement is false. -/
theorem v2s_amc12a_2020_p13_false :
    ¬ ∀ (a b c : ℕ) (_h₀ : 1 < a ∧ 1 < b ∧ 1 < c)
      (_h₁ : ∀ n : NNReal, n ≠ 1 → (n * (n * n ^ (1 / c)) ^ (1 / b)) ^ (1 / a) = (n ^ 25) ^ (1 / 36)),
      b = 3 := by
  intro h
  have := h 2 2 2 (by norm_num) (fun n _ => by norm_num)
  omega

/-- miniF2F-v2c `amc12a_2020_p13`: the multiple-choice version is false as well (`b = 7`). -/
theorem v2c_amc12a_2020_p13_false :
    ¬ ∀ (a b c : ℕ) (_h₀ : 1 < a ∧ 1 < b ∧ 1 < c)
      (_h₁ : ∀ n : NNReal, n ≠ 1 → (n * (n * n ^ (1 / c)) ^ (1 / b)) ^ (1 / a) = (n ^ 25) ^ (1 / 36)),
      b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 5 ∨ b = 6 := by
  intro h
  have := h 2 7 2 (by norm_num) (fun n _ => by norm_num)
  omega

/-- miniF2F-v2c `amc12a_2003_p25`: `{x | 0 ≤ f x}` compares the curried `f x : ℝ → ℝ → ℝ`
pointwise, so it is all of `ℝ`, never a range of `√·`; the answer set is empty, not of size 2. -/
theorem v2c_amc12a_2003_p25_empty (f : ℝ → ℝ → ℝ → ℝ) (S : Set ℝ)
    (h₀ : f = fun a b x ↦ Real.sqrt (a * x ^ 2 + b * x))
    (hS : S = {a | ∃ b, 0 < b ∧ Set.range (f a b) = { x | 0 ≤ f x }}) : S = ∅ := by
  subst hS h₀
  ext a
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_and]
  intro b _ h
  have hm : (-1 : ℝ) ∈ { x : ℝ | 0 ≤ (fun a b x ↦ Real.sqrt (a * x ^ 2 + b * x)) x } := by
    simp only [Set.mem_setOf_eq, Pi.le_def, Pi.zero_apply]
    intro b' y
    exact Real.sqrt_nonneg _
  rw [← h] at hm
  obtain ⟨y, hy⟩ := hm
  have := Real.sqrt_nonneg (a * y ^ 2 + b * y)
  simp only at hy
  linarith

/-- miniF2F-v2s `amc12a_2003_p25` (elaborated with the coercion `↑S`): false, since the set is empty. -/
theorem v2s_amc12a_2003_p25_false :
    ¬ ∀ (f : ℝ → ℝ → ℝ → ℝ) (S : Finset ℝ)
      (_h₀ : f = fun a b x ↦ Real.sqrt (a * x ^ 2 + b * x))
      (_hS : (S : Set ℝ) = {a | ∃ b, 0 < b ∧ Set.range (f a b) = { x | 0 ≤ f x }}), S.card = 2 := by
  intro h
  have := h _ ∅ rfl (Finset.coe_empty.trans (v2c_amc12a_2003_p25_empty _ _ rfl rfl).symm)
  simp at this

/-- PutnamBench `putnam_1991_a6`: `→` binds weaker than `∧`, so the set in `hA` contains every
tuple that is not a partition of `n`; it is infinite, contradicting `A n : ℕ`. -/
theorem putnam_1991_a6_vacuous (nabsum : ℕ → ℕ × (ℕ → ℕ) → Prop) (A : ℕ → ℕ)
    (hnabsum : ∀ᵉ (n ≥ 1) (ab), nabsum n ab ↔
      (ab.1 ≥ 1 ∧ (∀ i < ab.1, ab.2 i > 0) ∧
      (∀ i ≥ ab.1, ab.2 i = 0) ∧ (∑ i : Fin ab.1, ab.2 i) = n))
    (hA : ∀ n ≥ 1, A n = {a | nabsum n a ∧
      (∀ i : Fin (a.1 - 2), a.2 i > a.2 (i + 1) + a.2 (i + 2)) ∧ 1 < a.1 →
        a.2 (a.1 - 2) > a.2 (a.1 - 1)}.encard) : False := by
  have h := hA 1 le_rfl
  set S := {a : ℕ × (ℕ → ℕ) | nabsum 1 a ∧
      (∀ i : Fin (a.1 - 2), a.2 i > a.2 (i + 1) + a.2 (i + 2)) ∧ 1 < a.1 →
        a.2 (a.1 - 2) > a.2 (a.1 - 1)} with hS
  have hsub : Set.range (fun k : ℕ => ((0 : ℕ), fun _ : ℕ => k)) ⊆ S := by
    rintro _ ⟨k, rfl⟩ ⟨h1, _, _⟩
    have := ((hnabsum 1 le_rfl _).1 h1).1
    simp at this
  have hinf : (Set.range (fun k : ℕ => ((0 : ℕ), fun _ : ℕ => k))).Infinite :=
    Set.infinite_range_of_injective (fun x y hxy => by simpa using congrFun (congrArg Prod.snd hxy) 0)
  rw [(hinf.mono hsub).encard_eq] at h
  exact ENat.coe_ne_top _ h

/-- ProofNet# `Munkres exercise_24_3a`: without a type ascription `Icc 0 1` is taken in `ℕ`, a
two-point discrete space, and swapping its points is a continuous map without a fixed point. -/
theorem munkres_24_3a_false :
    ¬ ∀ (f : Set.Icc 0 1 → Set.Icc 0 1) (_hf : Continuous f), ∃ x : Set.Icc 0 1, f x = x := by
  intro h
  obtain ⟨⟨x, hx0, hx1⟩, hx⟩ := h (fun x => ⟨1 - x.1, by simp, by simp⟩) continuous_of_discreteTopology
  have := congrArg Subtype.val hx
  simp only at this
  omega

/-- ProofNet# `Munkres exercise_21_6b` (marked faithful by ProofNet-Verified): the same missing
ascription puts `Icc 0 1` in `ℕ`, so `x ^ n` is constant in `n ≥ 1` and the sequence converges
uniformly to `x ↦ x`. The statement claims it does not. -/
theorem munkres_21_6b_false :
    ¬ ∀ (f : ℕ → Set.Icc 0 1 → ℝ), (∀ x n, f n x = (x : ℕ) ^ n) →
      ¬ ∃ f₀, TendstoUniformly f f₀ Filter.atTop := by
  intro h
  apply h (fun n x => ((x : ℕ) : ℝ) ^ n) (fun _ _ => rfl)
  refine ⟨fun x => ((x : ℕ) : ℝ), ?_⟩
  have key : ∀ x : Set.Icc 0 1, ∀ n, 1 ≤ n → ((x : ℕ) : ℝ) ^ n = ((x : ℕ) : ℝ) := by
    rintro ⟨x, hx0, hx1⟩ n hn
    interval_cases x <;> simp [zero_pow (by omega : n ≠ 0)]
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn x
  rw [key x n hn, dist_self]
  exact hε

/-- ProofNet# `Munkres exercise_24_2`: the circle is formalized as `Metric.sphere 0 1 : Set ℝ`,
which is `{-1, 1}`, and the identity map takes different values at `x` and `-x`. -/
theorem munkres_24_2_false :
    ¬ ∀ {f : (Metric.sphere 0 1 : Set ℝ) → ℝ} (_hf : Continuous f), ∃ x, f x = f (-x) := by
  intro h
  obtain ⟨⟨x, hx⟩, hxx⟩ := h (f := fun x => (x : ℝ)) continuous_subtype_val
  have hn : ‖x‖ = 1 := by simpa using hx
  have : x = -x := by simpa using hxx
  have h0 : x = 0 := by linarith
  simp [h0] at hn

/-! ProofNet# references found false by pairwise rejects on ProofNetVerif (`npimp` and `rs`).
Each statement is the ProofNet# test statement verbatim, with `Type*` instantiated at `Type`. -/

/-- ProofNet# `Dummit_Foote exercise_2_1_13`: the hypothesis is stated for one `x`; with `x = 0` it
is vacuous, and `ℤ ≤ ℚ` is neither trivial nor everything. -/
theorem dummit_foote_2_1_13_false :
    ¬ ∀ (H : AddSubgroup ℚ) {x : ℚ} (_hH : (x ∈ H ∧ x ≠ 0) → (1 / x) ∈ H), H = ⊥ ∨ H = ⊤ := by
  intro h
  rcases h (AddSubgroup.zmultiples (1 : ℚ)) (x := 0) (fun hx => absurd rfl hx.2) with h | h
  · have : (1 : ℚ) ∈ AddSubgroup.zmultiples (1 : ℚ) := AddSubgroup.mem_zmultiples 1
    rw [h, AddSubgroup.mem_bot] at this
    exact one_ne_zero this
  · have : (1 / 2 : ℚ) ∈ AddSubgroup.zmultiples (1 : ℚ) := h ▸ AddSubgroup.mem_top _
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.1 this
    have hk' : ((2 * k : ℤ) : ℚ) = 1 := by push_cast; rw [← zsmul_one, hk]; norm_num
    have : 2 * k = 1 := by exact_mod_cast hk'
    omega

/-- A type with the indiscrete topology. -/
def Indisc (α : Type) : Type := α

instance (α : Type) : TopologicalSpace (Indisc α) := ⊤

theorem Indisc.isOpen_iff {α : Type} (U : Set (Indisc α)) : IsOpen U ↔ U = ∅ ∨ U = Set.univ :=
  TopologicalSpace.isOpen_top_iff (α := α) U

/-- ProofNet# `Pugh exercise_2_92`: without a Hausdorff assumption nested nonempty compact sets
can have empty intersection: the tails of `ℕ` with the indiscrete topology. -/
theorem pugh_2_92_false :
    ¬ ∀ {α : Type} [_t : TopologicalSpace α] {s : ℕ → Set α} (_hs : ∀ i, IsCompact (s i))
      (_hne : ∀ i, (s i).Nonempty) (_hs : ∀ i, (s i) ⊇ (s (i + 1))), (⋂ i, s i).Nonempty := by
  intro h
  have hn : ∀ a : Indisc ℕ, nhds a = ⊤ := fun _ => nhds_top
  obtain ⟨x, hx⟩ := h (α := Indisc ℕ) (s := fun i => {n : Indisc ℕ | i ≤ show ℕ from n})
    (fun i => isCompact_iff_ultrafilter_le_nhds.2 fun _ _ =>
      ⟨show Indisc ℕ from i, le_refl i, by rw [hn]; exact le_top⟩)
    (fun i => ⟨show Indisc ℕ from i, le_refl i⟩) (fun i _ hn => Nat.le_of_succ_le hn)
  have := Set.mem_iInter.1 hx ((show ℕ from x) + 1)
  exact Nat.not_succ_le_self _ this

/-- ProofNet# `Herstein exercise_2_3_16`: the trivial group has no proper nontrivial subgroup,
but its order is not prime. -/
theorem herstein_2_3_16_false :
    ¬ ∀ {G : Type} [Group G] (_hG : ∀ H : Subgroup G, H = ⊤ ∨ H = ⊥),
      IsCyclic G ∧ ∃ (p : ℕ) (Fin : Fintype G), Nat.Prime p ∧ @Fintype.card G Fin = p := by
  intro h
  obtain ⟨_, p, F, hp, hc⟩ := h (G := Unit) (fun _ => Or.inl (Subsingleton.elim _ _))
  have h1 : @Fintype.card Unit F = 1 := by convert Fintype.card_unit
  rw [← hc, h1] at hp
  exact Nat.not_prime_one hp

/-- ProofNet# `Herstein exercise_2_7_7`: `φ` is not assumed surjective; the inclusion of a
non-normal subgroup maps the normal subgroup `⊤` onto it. -/
theorem herstein_2_7_7_false :
    ¬ ∀ {G : Type} [Group G] {G' : Type} [Group G'] (φ : G →* G') (N : Subgroup G) [N.Normal],
      (Subgroup.map φ N).Normal := by
  intro h
  set s : Equiv.Perm (Fin 3) := Equiv.swap 0 1
  set H := Subgroup.zpowers s
  have hn := (h H.subtype ⊤).conj_mem s ⟨⟨s, Subgroup.mem_zpowers s⟩, trivial, rfl⟩ (Equiv.swap 1 2)
  obtain ⟨⟨y, k, hk⟩, _, hy⟩ := hn
  have h2 : (s ^ k) 2 = 2 := Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self (by decide) k
  have hk' : s ^ k = y := hk
  simp only [Subgroup.coe_subtype] at hy
  rw [hk', hy] at h2
  revert h2
  decide

/-- ProofNet# `Rudin exercise_1_8`: every set carries a linear order; the statement needs the
order to be compatible with the field operations. -/
theorem rudin_1_8_false : ¬ ¬ ∃ (r : ℂ → ℂ → Prop), IsLinearOrder ℂ r := by
  intro h
  apply h
  letI : LinearOrder ℂ := LinearOrder.lift' (fun z : ℂ => toLex (z.re, z.im)) fun a b hab => by
    simp only [toLex_inj, Prod.mk.injEq] at hab
    exact Complex.ext hab.1 hab.2
  exact ⟨(· ≤ ·), inferInstance⟩

/-- ProofNet# `Rudin exercise_4_15`: `Monotone` is "nondecreasing", not "monotonic"; `x ↦ -x` is
a continuous open map. -/
theorem rudin_4_15_false :
    ¬ ∀ {f : ℝ → ℝ} (_hf : Continuous f) (_hof : IsOpenMap f), Monotone f := by
  intro h
  have := h (f := fun x => -x) continuous_neg (Homeomorph.neg ℝ).isOpenMap (show (0 : ℝ) ≤ 1 by norm_num)
  norm_num at this

/-- ProofNet# `Munkres exercise_31_1`: `RegularSpace` does not include `T₁`; two points of the
indiscrete `Bool` have no separating neighbourhoods. -/
theorem munkres_31_1_false :
    ¬ ∀ {X : Type} [_t : TopologicalSpace X] (_hX : RegularSpace X) (x y : X) (_hxy : x ≠ y),
      ∃ (U V : Set X), IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ y ∈ V ∧ closure U ∩ closure V = ∅ := by
  intro h
  have hreg : RegularSpace (Indisc Bool) := by
    refine ⟨fun {s a} hs ha => ?_⟩
    rcases (Indisc.isOpen_iff sᶜ).1 hs.isOpen_compl with h0 | h0
    · exact absurd ((Set.compl_empty_iff.1 h0) ▸ Set.mem_univ a) ha
    · rw [Set.compl_univ_iff.1 h0, nhdsSet_empty]
      exact disjoint_bot_left
  obtain ⟨U, V, hU, hV, hxU, hyV, hUV⟩ :=
    h (X := Indisc Bool) hreg (show Indisc Bool from true) (show Indisc Bool from false)
      (show (true : Bool) ≠ false by decide)
  rcases (Indisc.isOpen_iff U).1 hU with rfl | rfl
  · exact hxU
  rcases (Indisc.isOpen_iff V).1 hV with rfl | rfl
  · exact hyV
  rw [closure_univ, Set.univ_inter] at hUV
  rw [hUV] at hxU
  exact hxU

/-- ProofNet# `Ireland_Rosen exercise_4_6`: the order of the primitive root is written `p`
instead of `p - 1`; for `p = 3` the element `3` is `0`. -/
theorem ireland_rosen_4_6_false :
    ¬ ∀ {p n : ℕ} (_hp : p.Prime) (_hpn : p = 2 ^ n + 1), IsPrimitiveRoot (3 : ZMod p) p := by
  intro h
  have := (h (p := 3) (n := 1) Nat.prime_three rfl).pow_eq_one
  revert this
  decide

/-- ProofNet# `Putnam exercise_2014_a5`: the summand is `X ^ n` instead of `X ^ i`, so `P 1` and
`P 2` both vanish at `0` and are not coprime. -/
theorem putnam_2014_a5_false :
    ¬ ∀ (P : ℕ → Polynomial ℤ) (_hP : ∀ n, P n = ∑ i : Fin n, (n + 1) * Polynomial.X ^ n),
      ∀ (j k : ℕ), j ≠ k → IsCoprime (P j) (P k) := by
  intro h
  obtain ⟨a, b, hab⟩ := h _ (fun _ => rfl) 1 2 (by decide)
  have := congrArg (Polynomial.eval 0) hab
  simp at this

/-- ProofNet# `Rudin exercise_2_29`: the intervals are bounded, and `ℝ` is no disjoint union of
bounded open intervals: the right end of the one containing `0` is covered by another. -/
theorem rudin_2_29_false :
    ¬ ∀ (U : Set ℝ) (_hU : IsOpen U), ∃ (f : ℕ → Set ℝ),
      (∀ n, ∃ a b : ℝ, f n = {x | a < x ∧ x < b}) ∧ (∀ n, f n ⊆ U) ∧
      (∀ n m, n ≠ m → f n ∩ f m = ∅) ∧ U = ⋃ n, f n := by
  intro h
  obtain ⟨f, hf, -, hdisj, hU⟩ := h Set.univ isOpen_univ
  obtain ⟨n, hn⟩ := Set.mem_iUnion.1 (hU ▸ Set.mem_univ (0 : ℝ))
  obtain ⟨a, b, hab⟩ := hf n
  obtain ⟨m, hm⟩ := Set.mem_iUnion.1 (hU ▸ Set.mem_univ b)
  obtain ⟨a', b', hab'⟩ := hf m
  rw [hab] at hn
  have hnm : n ≠ m := by
    rintro rfl
    rw [hab] at hm
    exact lt_irrefl _ hm.2
  rw [hab'] at hm
  simp only [Set.mem_setOf_eq] at hn hm
  have ht : (max a a' + b) / 2 ∈ f n ∩ f m := by
    rw [Set.mem_inter_iff, hab, hab']
    simp only [Set.mem_setOf_eq]
    have h1 := le_max_left a a'
    have h2 := le_max_right a a'
    have h3 : max a a' < b := max_lt (hn.1.trans hn.2) hm.1
    refine ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  rw [hdisj n m hnm] at ht
  exact ht

end BenchErrors
