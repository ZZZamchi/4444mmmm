# Blind annotation sheet (E3)

For every item: read NL, G (reference) and P (candidate). Answer the questions for the item's set.
Do not consult any tool output. Record answers as JSON `{item_id: {...}}`.

Set A/B question: `equivalent` (true/false): are G and P equivalent formalizations of NL?
If false, `kind`: `label_error` (one side is wrong w.r.t. NL), `hyp_diff` (hypotheses differ, both
defensible), `conclusion_diff`, `type_drift` (same statement on a different type), `other`.
Set C question: `label_correct` (true/false): the dataset label says G and P are NOT equivalent; is that right?

## item 01  [pnv-test-754]  set B

**NL.** Let $f$ be a continuous real function on a metric space $X$. Let $Z(f)$ (the zero set of $f$ ) be the set of all $p \in X$ at which $f(p)=0$. Prove that $Z(f)$ is closed.

```lean
theorem exercise_4_3
  {α : Type} [MetricSpace α]
  (f : α → ℝ) (h : Continuous f) (z : Set α) (g : z = f⁻¹' {0})
  : IsClosed z := sorry
```

```lean
theorem dummy {X : Type*} [TopologicalSpace X] [T2Space X] {f : X → ℝ} (hf : Continuous f) : IsClosed {p : X | f p = 0} := sorry
```

## item 02  [pnv-test-1042]  set B

**NL.** Let $\varphi: R \rightarrow S$ be a surjective homomorphism of rings. Prove that the image of the center of $R$ is contained in the center of $S$.

```lean
theorem exercise_7_3_16 {R S : Type*} [Ring R] [Ring S]
  {φ : R →+* S} (hf : Function.Surjective φ) :
  φ '' (center R) ⊆ center S := sorry
```

```lean
theorem dummy {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (hφ : Function.Surjective φ) : (φ '' (center R)) ⊆ center S := sorry
```

## item 03  [pnv-test-186]  set C

**NL.** Prove that as vector spaces over $\mathbb{Q}, \mathbb{R}^n \cong \mathbb{R}$, for all $n \in \mathbb{Z}^{+}$.

```lean
theorem exercise_11_1_13 {n : ℕ+} :
  Nonempty ((Fin n → ℝ) ≃ₗ[ℚ] ℝ) := sorry
```

```lean
theorem dummy (n : ℕ) : ∃ (f : ℝ ≃ₗ[ℚ] Fin n → ℝ), True := sorry
```

## item 04  [pnv-test-406]  set B

**NL.** If $a \in K$ is such that $a^2$ is algebraic over the subfield $F$ of $K$, show that a is algebraic over $F$.

```lean
theorem exercise_5_3_7 {K : Type*} [Field K] {F : Subfield K}
  {a : K} (ha : IsAlgebraic F (a ^ 2)) : IsAlgebraic F a := sorry
```

```lean
theorem dummy {K : Type*} [Field K] {F : Type*} [Field F] [Algebra F K] (a : K) (ha : IsAlgebraic F (a ^ 2)) : IsAlgebraic F a := sorry
```

## item 05  [pnv-test-1007]  set C

**NL.** Show that if $\prod X_\alpha$ is normal, then so is $X_\alpha$. Assume that each $X_\alpha$ is nonempty.

```lean
theorem exercise_32_2c
  {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
  (h : ∀ i, Nonempty (X i)) (h2 : NormalSpace (Π i, X i)) :
  ∀ i, NormalSpace (X i) := sorry
```

```lean
theorem dummy {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)] (h : NormalSpace (Π i, X i)) (i : ι) : NormalSpace (X i) := sorry
```

## item 06  [pnv-test-1098]  set B

**NL.** Prove that the multiplication of residue class $\mathbb{Z}/n\mathbb{Z}$ is associative.

```lean
theorem exercise_1_1_4 (n : ℕ) (a b c : ZMod n) :
  (a * b) * c = a * (b * c) := sorry
```

```lean
theorem dummy (n : ℕ) (a b c : ℤ) : (a * b)%n * c %n = a * (b * c) %n := sorry
```

## item 07  [pnv-test-693]  set A

**NL.** Prove that if $a \in \mathbf{F}$, $v \in V$, and $av = 0$, then $a = 0$ or $v = 0$.

```lean
theorem exercise_1_4 {F V : Type*} [AddCommGroup V] [Field F]
  [Module F V] (v : V) (a : F): a • v = 0 → a = 0 ∨ v = 0 := sorry
```

```lean
theorem dummy {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V] (a : F) (v : V) : a • v = 0 ↔ a = 0 ∨ v = 0 := sorry
```

## item 08  [pnv-test-41]  set C

**NL.** Let $p: X \rightarrow Y$ be a closed continuous surjective map such that $p^{-1}(\{y\})$ is compact, for each $y \in Y$. (Such a map is called a perfect map.) Show that if $Y$ is compact, then $X$ is compact.

```lean
theorem exercise_26_12 {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  (p : X → Y) (h : Function.Surjective p) (hc : Continuous p)
  (hp : IsClosedMap p) (hp : ∀ y, IsCompact (p ⁻¹' {y}))
  (hY : CompactSpace Y) : CompactSpace X := sorry
```

```lean
theorem dummy {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (p : X → Y) (h : CompactSpace Y) (h' : Continuous p) (h'' : Function.Surjective p) (hc : ∀ y : Y, IsCompact (p ⁻¹' {y})) : CompactSpace X := sorry
```

## item 09  [pnv-test-695]  set A

**NL.** Prove that $\sum 1/k(\log(k))^p$ converges when $p > 1$.

```lean
theorem exercise_3_63a (p : ℝ) (f : ℕ → ℝ) (hp : p > 1)
  (h : f = λ (k : ℕ) => (1 : ℝ) / (k * (log k) ^ p)) :
  ∃ l, Tendsto f atTop (𝓝 l) := sorry
```

```lean
theorem dummy (p : ℝ) (hp : 1 < p) : Summable fun k => 1 / (k * (log k)^p) := sorry
```

## item 10  [pnv-test-311]  set A

**NL.** Let $H$ be a subgroup of the additive group of rational numbers with the property that $1 / x \in H$ for every nonzero element $x$ of $H$. Prove that $H=0$ or $\mathbb{Q}$.

```lean
theorem exercise_2_1_13 (H : AddSubgroup ℚ) {x : ℚ}
  (hH : (x ∈ H ∧ x ≠ 0) → (1 / x) ∈ H):
  H = ⊥ ∨ H = ⊤ := sorry
```

```lean
theorem dummy {H : AddSubgroup ℚ} (h : ∀ x ∈ H, x ≠ 0 → 1 / x ∈ H) : H = ⊥ ∨ H = ⊤ := sorry
```

## item 11  [pnv-test-717]  set C

**NL.** Show that the collection $\{(a,b) \mid a < b, a \text{ and } b \text{ rational}\}$ is a basis that generates the standard topology on $\mathbb{R}$.

```lean
theorem exercise_13_8a :
  IsTopologicalBasis {S : Set ℝ | ∃ a b : ℚ, a < b ∧ S = Ioo ↑a ↑b} := sorry
```

```lean
theorem dummy (x : ℝ) : ∃ (a b : ℕ), b > a ∧ ∀ (A : Set ℝ), IsOpen A ∧ x ∈ A ↔ (∃ (n : ℕ), (a : ℝ) ≤ n ∧ n < b ∧ (n : ℝ) ∈ A) := sorry
```

## item 12  [pnv-test-769]  set B

**NL.** Deduce that $|a b|=|b a|$ for all $a, b \in G$.

```lean
theorem exercise_1_1_22b {G: Type*} [Group G] (a b : G) :
  orderOf (a * b) = orderOf (b * a) := sorry
```

```lean
theorem dummy {G : Type*} [Group G] {a b c : G} : a * b = a * c → b = c := sorry
```

## item 13  [pnv-test-1441]  set B

**NL.** If $a \in K$ is such that $a^2$ is algebraic over the subfield $F$ of $K$, show that a is algebraic over $F$.

```lean
theorem exercise_5_3_7 {K : Type*} [Field K] {F : Subfield K}
  {a : K} (ha : IsAlgebraic F (a ^ 2)) : IsAlgebraic F a := sorry
```

```lean
theorem dummy {F K : Type*} [Field F] [Field K] [Algebra F K] {a : K} (h : IsAlgebraic F (a^2)) : IsAlgebraic F a := sorry
```

## item 14  [pnv-test-643]  set C

**NL.** For any two real sequences $\left\{a_{n}\right\},\left\{b_{n}\right\}$, prove that $\limsup _{n \rightarrow \infty}\left(a_{n}+b_{n}\right) \leq \limsup _{n \rightarrow \infty} a_{n}+\limsup _{n \rightarrow \infty} b_{n},$ provided the sum on the right is not of the form $\infty-\infty$.

```lean
theorem exercise_3_5
    (a b : ℕ → EReal)
    (hareal : ∀ n, a n ≠ ⊤ ∧ a n ≠ ⊥)
    (hbreal : ∀ n, b n ≠ ⊤ ∧ b n ≠ ⊥)
    (ha : limsup a ≠ ⊤)
    (hb : limsup b ≠ ⊥) :
    limsup (λ n => a n + b n) ≤ limsup a + limsup b := sorry
```

```lean
theorem dummy {a b : ℕ → ℝ} (haa : Tendsto a atTop atTop) (hbb : Tendsto b atTop atTop) (ha : ∃ l, Tendsto a atTop (𝓝 l)) (hb : ∃ l, Tendsto b atTop (𝓝 l)) : limsup (a + b) ≤ limsup a + limsup b := sorry
```

## item 15  [pnv-test-453]  set B

**NL.** Prove that the union of two subspaces of $V$ is a subspace of $V$ if and only if one of the subspaces is contained in the other.

```lean
theorem exercise_1_9 {F V : Type*} [AddCommGroup V] [Field F]
  [Module F V] (U W : Submodule F V):
  (∃ U' : Submodule F V, U'.carrier = ↑U ∪ ↑W) ↔ (U ≤ W ∨ W ≤ U) := sorry
```

```lean
theorem dummy {V : Type*} [AddCommGroup V] [Module ℤ V] (W₁ W₂ : Submodule ℤ V) : (W₁ ≤ W₂) ∧ (W₂ ≤ W₁) → (W₁ ⊔ W₂ = W₁) ∨ (W₁ ⊔ W₂ = W₂) := sorry
```

## item 16  [pnv-test-1355]  set B

**NL.** Use Lagrange's Theorem in the multiplicative group $(\mathbb{Z} / p \mathbb{Z})^{\times}$to prove Fermat's Little Theorem: if $p$ is a prime then $a^{p} \equiv a(\bmod p)$ for all $a \in \mathbb{Z}$.

```lean
theorem exercise_3_2_16 (p : ℕ) (hp : Nat.Prime p) (a : ℤ) :
  a ^ p ≡ a [ZMOD p] := sorry
```

```lean
theorem dummy (p : ℕ) [Fact (Nat.Prime p)] (a : ℕ) : a ^ p ≡ a [MOD p] := sorry
```

## item 17  [pnv-test-913]  set A

**NL.** Suppose $T \in \mathcal{L}(V)$ is such that every subspace of $V$ with dimension $\operatorname{dim} V-1$ is invariant under $T$. Prove that $T$ is a scalar multiple of the identity operator.

```lean
theorem exercise_5_13 {F V : Type*} [AddCommGroup V] [Field F]
  [Module F V] [FiniteDimensional F V] {T : End F V}
  (hS : ∀ U : Submodule F V, finrank F U = finrank F V - 1 →
  Submodule.map T U = U) : ∃ c : F, T = c • LinearMap.id := sorry
```

```lean
theorem dummy {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] (T : End K V) (h : ∀ (U : Subspace K V), finrank K V - 1 = finrank K U → T '' U ≤ U) : ∃ (c : K), T = c • 1 := sorry
```

## item 18  [pnv-test-992]  set A

**NL.** Give a direct proof that the nested decreasing intersection of nonempty covering compact sets is nonempty.

```lean
theorem exercise_2_92 {α : Type*} [TopologicalSpace α]
  {s : ℕ → Set α}
  (hs : ∀ i, IsCompact (s i))
  (hne : ∀ i, (s i).Nonempty)
  (hs : ∀ i, (s i) ⊇ (s (i + 1))) :
  (⋂ i, s i).Nonempty := sorry
```

```lean
theorem dummy {α : Type*} [TopologicalSpace α] [CompactSpace α] {K : ℕ → Set α} (hK : ∀ n, IsCompact (K n)) (hdec : ∀ n, K (n + 1) ⊆ K n) (hne : ∀ n, (K n).Nonempty) : (⋂ n, K n).Nonempty := sorry
```

## item 19  [pnv-test-1026]  set A

**NL.** Prove that there exists a normal subgroup that is not characteristic.

```lean
theorem exercise_4_4_6b :
  ∃ (G : Type*) (hG : Group G) (H : @Subgroup G hG), @Normal G hG H ∧ ¬ @Characteristic G hG H := sorry
```

```lean
theorem dummy (G : Type*) [Group G] : ∃ H : Subgroup G, H.Normal ∧ ¬ H.Characteristic := sorry
```

## item 20  [pnv-test-1171]  set C

**NL.** Prove that there are unique positive integers $a, n$ such that $a^{n+1}-(a+1)^n=2001$.

```lean
theorem exercise_2001_a5 :
  ∃! p : ℕ × ℕ, p.1 > 0 ∧ p.2 > 0 ∧ p.1^(p.2 + 1) - (p.1 + 1)^(p.2) = 2001 := sorry
```

```lean
theorem dummy {a : ℕ} (ha : 0 < a) : ∃! (n : ℕ), a ^ (n + 1) - (a + 1) ^ n = 2001 := sorry
```

## item 21  [pnv-test-576]  set A

**NL.** Suppose $g$ is a real function on $R^{1}$, with bounded derivative (say $\left|g^{\prime}\right| \leq M$ ). Fix $\varepsilon>0$, and define $f(x)=x+\varepsilon g(x)$. Prove that $f$ is one-to-one if $\varepsilon$ is small enough.

```lean
theorem exercise_5_3 {g : ℝ → ℝ} (hg : Continuous g)
  (hg' : ∃ M : ℝ, ∀ x : ℝ, |deriv g x| ≤ M) :
  ∃ N, ∀ ε > 0, ε < N → Function.Injective (λ x : ℝ => x + ε * g x) := sorry
```

```lean
theorem dummy {g : ℝ → ℝ} (M : ℝ) (hM : ∀ x, |deriv g x| ≤ M) (ε : ℝ) (hε : ε > 0) (f : ℝ → ℝ) (hf : ∀ x, f x = x + ε * g x) : ∃ δ > 0, (ε < δ) → Function.Injective f := sorry
```

## item 22  [pnv-test-1427]  set C

**NL.** Let $f: \mathbb{R} \rightarrow \mathbb{R}$ be an infinitely differentiable function satisfying $f(0)=0, f(1)=1$, and $f(x) \geq 0$ for all $x \in$ $\mathbb{R}$. Show that there exist a positive integer $n$ and a real number $x$ such that $f^{(n)}(x)<0$.

```lean
theorem exercise_2018_a5 (f : ℝ → ℝ) (hf : ContDiff ℝ ⊤ f)
  (hf0 : f 0 = 0) (hf1 : f 1 = 1) (hf2 : ∀ x, f x ≥ 0) :
  ∃ (n : ℕ+) (x : ℝ), iteratedDeriv n f x < 0 := sorry
```

```lean
theorem dummy {f : ℝ → ℝ} (hf : ContDiff ℝ ⊤ f) (hf₀ : f 0 = 0) (hf₁ : f 1 = 1) (hf₂ : ∀ x, 0 ≤ f x) : ∃ n : ℕ, ∃ x : ℝ, f ^[n] x < 0 := sorry
```

## item 23  [pnv-test-892]  set B

**NL.** Prove that every compact metric space $K$ has a countable base.

```lean
theorem exercise_2_25 {K : Type*} [MetricSpace K] [CompactSpace K] :
  ∃ (B : Set (Set K)), Set.Countable B ∧ IsTopologicalBasis B := sorry
```

```lean
theorem dummy {K : Type*} [TopologicalSpace K] [CompactSpace K] [MetrizableSpace K] : ∃ b : Set (Set K), (∀ s ∈ b, IsOpen s) ∧ (∀ t, IsOpen t → ∃ u ⊆ b, ⋃₀ u = t) ∧ Countable b := sorry
```

## item 24  [pnv-test-231]  set C

**NL.** Prove that there are unique positive integers $a, n$ such that $a^{n+1}-(a+1)^n=2001$.

```lean
theorem exercise_2001_a5 :
  ∃! p : ℕ × ℕ, p.1 > 0 ∧ p.2 > 0 ∧ p.1^(p.2 + 1) - (p.1 + 1)^(p.2) = 2001 := sorry
```

```lean
theorem dummy (a n : ℕ) (ha : 0 < a) (hn : 0 < n) : a^(n+1) - (a+1)^n = 2001 := sorry
```

## item 25  [pnv-test-1072]  set C

**NL.** If $\left\{E_{n}\right\}$ is a sequence of closed nonempty and bounded sets in a complete metric space $X$, if $E_{n} \supset E_{n+1}$, and if $\lim _{n \rightarrow \infty} \operatorname{diam} E_{n}=0,$ then $\bigcap_{1}^{\infty} E_{n}$ consists of exactly one point.

```lean
theorem exercise_3_21
  {X : Type*} [MetricSpace X] [CompleteSpace X]
  (E : ℕ → Set X)
  (hEcl : ∀ n, IsClosed (E n))
  (hEne : ∀ n, (E n).Nonempty)
  (hEbdd : ∀ n, Bornology.IsBounded (E n))
  (hE : ∀ n, E n ⊇ E (n + 1))
  (hE' : Tendsto (λ n => Metric.diam (E n)) atTop (𝓝 0)) :
  ∃ a, Set.iInter E = {a} := sorry
```

```lean
theorem dummy {X : Type u} [MetricSpace X] {s t : Set X} (hs : IsClosed s) (ht : IsClosed t) (h's : Set.Nonempty s) (h't : Set.Nonempty t) : (∃ x ∈ s, ∃ y ∈ t, x = y) ↔ s = t := sorry
```

## item 26  [pnv-test-297]  set C

**NL.** If $P \triangleleft G$, $P$ a $p$-Sylow subgroup of $G$, prove that $\varphi(P) = P$ for every automorphism $\varphi$ of $G$.

```lean
theorem exercise_2_11_7 {G : Type*} [Group G] {p : ℕ} (hp : Nat.Prime p)
  {P : Sylow p G} (hP : P.Normal) :
  Subgroup.Characteristic (P : Subgroup G) := sorry
```

```lean
theorem dummy {G : Type*} [Group G] [Fintype G] {p : ℕ} [hp : Fact p.Prime] {P : Sylow p G} (f : G ≃* G) : ↑f '' P = P := sorry
```

## item 27  [pnv-test-93]  set C

**NL.** A subgroup $M$ of a group $G$ is called a maximal subgroup if $M \neq G$ and the only subgroups of $G$ which contain $M$ are $M$ and $G$. Prove that if $H$ is a proper subgroup of the finite group $G$ then there is a maximal subgroup of $G$ containing $H$.

```lean
theorem exercise_2_4_16a {G : Type*} [Group G] [Fintype G] {H : Subgroup G}
  (hH : H ≠ ⊤) :
  ∃ M : Subgroup G, M ≠ ⊤ ∧
  (∀ K : Subgroup G, M ≤ K → K = M ∨ K = ⊤) ∧
  H ≤ M := sorry
```

```lean
theorem dummy {G : Type*} [Group G] [Finite G] {H : Subgroup G} (hH : H ≠ ⊤) : ∃ (M : Subgroup G), H ≤ M ∧ M ≠ ⊤ ∧ ∀ (K : Subgroup G), H ≤ K → K = M ∨ K = ⊤ := sorry
```

## item 28  [pnv-test-358]  set A

**NL.** If $k = 1$ and $\mathbf{x} \in R^{k}$, $\mathbf{x} \neq 0$, prove that there does not exist $\mathbf{y} \in R^{k}$ such that $\mathbf{y} \neq 0$ but $\mathbf{x} \cdot \mathbf{y}=0$

```lean
theorem exercise_1_18b
  : ∀ (x : ℝ), x ≠ 0 → ¬ ∃ (y : ℝ), y ≠ 0 ∧ x * y = 0 := sorry
```

```lean
theorem dummy {x y : ℝ} (hx : x ≠ 0) (hxy : x * y = 0) : y = 0 := sorry
```

## item 29  [pnv-test-253]  set A

**NL.** Give a direct proof that the nested decreasing intersection of nonempty covering compact sets is nonempty.

```lean
theorem exercise_2_92 {α : Type*} [TopologicalSpace α]
  {s : ℕ → Set α}
  (hs : ∀ i, IsCompact (s i))
  (hne : ∀ i, (s i).Nonempty)
  (hs : ∀ i, (s i) ⊇ (s (i + 1))) :
  (⋂ i, s i).Nonempty := sorry
```

```lean
theorem dummy {α : Type*} [TopologicalSpace α] [CompactSpace α] {K : ℕ → Set α} (hK : ∀ n, IsCompact (K n)) (hne : ∀ n, (K n).Nonempty) (hdec : ∀ n, K (n + 1) ⊆ K n) : (⋂ n, K n).Nonempty := sorry
```

## item 30  [pnv-test-1114]  set A

**NL.** Give a direct proof that the nested decreasing intersection of nonempty covering compact sets is nonempty.

```lean
theorem exercise_2_92 {α : Type*} [TopologicalSpace α]
  {s : ℕ → Set α}
  (hs : ∀ i, IsCompact (s i))
  (hne : ∀ i, (s i).Nonempty)
  (hs : ∀ i, (s i) ⊇ (s (i + 1))) :
  (⋂ i, s i).Nonempty := sorry
```

```lean
theorem dummy {α : Type*} [TopologicalSpace α] [CompactSpace α] {K : ℕ → Set α} (hK : ∀ n, IsCompact (K n)) (hK_nonempty : ∀ n, (K n).Nonempty) (hK_decreasing : ∀ n, K (n + 1) ⊆ K n) : (⋂ n, K n).Nonempty := sorry
```

## item 31  [pnv-test-796]  set B

**NL.** Use Lagrange's Theorem in the multiplicative group $(\mathbb{Z} / p \mathbb{Z})^{\times}$to prove Fermat's Little Theorem: if $p$ is a prime then $a^{p} \equiv a(\bmod p)$ for all $a \in \mathbb{Z}$.

```lean
theorem exercise_3_2_16 (p : ℕ) (hp : Nat.Prime p) (a : ℤ) :
  a ^ p ≡ a [ZMOD p] := sorry
```

```lean
theorem dummy (p : ℕ) [Fact p.Prime] (a : ℕ) : a ^ p ≡ a [MOD p] := sorry
```

## item 32  [pnv-test-1135]  set A

**NL.** If $G$ is a finite group, prove that, given $a \in G$, there is a positive integer $n$, depending on $a$, such that $a^n = e$.

```lean
theorem exercise_2_1_26 {G : Type*} [Group G]
  [Fintype G] (a : G) : ∃ (n : ℕ), n > 0 ∧ a ^ n = 1 := sorry
```

```lean
theorem dummy {G : Type*} [Group G] [Finite G] (a : G) : ∃ n : ℕ, n ≠ 0 ∧ a ^ n = 1 := sorry
```

## item 33  [pnv-test-532]  set B

**NL.** If $a \in K$ is such that $a^2$ is algebraic over the subfield $F$ of $K$, show that a is algebraic over $F$.

```lean
theorem exercise_5_3_7 {K : Type*} [Field K] {F : Subfield K}
  {a : K} (ha : IsAlgebraic F (a ^ 2)) : IsAlgebraic F a := sorry
```

```lean
theorem dummy {F K : Type*} [Field F] [Field K] [Algebra F K] (a : K) (h : IsAlgebraic F (a^2)) : IsAlgebraic F a := sorry
```

## item 34  [pnv-test-607]  set C

**NL.** Let $(X, d)$ be a metric space. If $f: X \rightarrow X$ satisfies the condition $d(f(x), f(y))=d(x, y)$ for all $x, y \in X$, then $f$ is called an isometry of $X$. Show that if $f$ is an isometry and $X$ is compact, then $f$ is bijective and hence a homeomorphism.

```lean
theorem exercise_28_6 {X : Type*} [MetricSpace X]
  [CompactSpace X] {f : X → X} (hf : Isometry f) :
  Continuous f ∧ Bijective f ∧ IsOpenMap f := sorry
```

```lean
theorem dummy {X : Type u} [MetricSpace X] (f : X → X) (hf : ∀ x y : X, dist (f x) (f y) = dist x y) (hX : CompactSpace X) : Function.Bijective f := sorry
```

## item 35  [pnv-test-628]  set C

**NL.** Suppose $f$ is a real, three times differentiable function on $[-1,1]$, such that $f(-1)=0, \quad f(0)=0, \quad f(1)=1, \quad f^{\prime}(0)=0 .$ Prove that $f^{(3)}(x) \geq 3$ for some $x \in(-1,1)$.

```lean
theorem exercise_5_17
  {f : ℝ → ℝ}
  (hf' : DifferentiableOn ℝ f (Set.Icc (-1) 1))
  (hf'' : DifferentiableOn ℝ (deriv f) (Set.Icc (-1) 1))
  (hf''' : DifferentiableOn ℝ (deriv (deriv f)) (Set.Icc (-1) 1))
  (hf0 : f (-1) = 0)
  (hf1 : f 0 = 0)
  (hf2 : f 1 = 1)
  (hf3 : deriv f 0 = 0) :
  ∃ x, x ∈ Set.Ioo (-1 : ℝ) 1 ∧ deriv (deriv (deriv f)) x ≥ 3 := sorry
```

```lean
theorem dummy {f : ℝ → ℝ} (h₁ : ContDiff ℝ 3 f) (h₂ : f (-1) = 0) (h₃ : f 0 = 0) (h₄ : f 1 = 1) (h₅ : deriv f 0 = 0) : ∃ x ∈ Set.Icc (-1 : ℝ) 1, deriv^[3] f x ≥ 3 := sorry
```

## item 36  [pnv-test-123]  set C

**NL.** If $F$ is of characteristic $p \neq 0$, show that all the roots of $x^m - x$, where $m = p^n$, are distinct.

```lean
theorem exercise_5_6_14 {p m n: ℕ} (hp : p ≠ 0) (hn : n > 0)
  {F : Type*} [Field F] [CharP F p] (hm : m = p ^ n) :
  (X ^ m - X : Polynomial F).Separable := sorry
```

```lean
theorem dummy {F : Type*} [Field F] {p n : ℕ} [hf : CharP F p] : ∀ m : ℕ, m = p^n → ∀ x y : F, x^m = x → y^m = y → x = y := sorry
```

## item 37  [pnv-test-604]  set C

**NL.** Let $f \colon X \rightarrow X$ be continuous. Show that if $X = [0, 1]$, there is a point $x$ such that $f(x) = x$. (The point $x$ is called a fixed point of $f$.)

```lean
theorem exercise_24_3a (f : Icc 0 1 → Icc 0 1) (hf : Continuous f) :
  ∃ (x : Icc 0 1), f x = x := sorry
```

```lean
theorem dummy {f : ℝ → ℝ} (hf : Continuous f) (h : ∀ x, 0 ≤ x ∧ x ≤ 1 → 0 ≤ f x ∧ f x ≤ 1) : ∃ x ∈ Icc (0 : ℝ) 1, f x = x := sorry
```

## item 38  [pnv-test-866]  set B

**NL.** Let $x$ be an element of $G$. Prove that if $|x|=n$ for some positive integer $n$ then $x^{-1}=x^{n-1}$.

```lean
theorem exercise_1_1_17 {G : Type*} [Group G] {x : G} {n : ℕ+}
  (hxn: orderOf x = n) :
  x⁻¹ = x ^ (n - 1 : ℕ) := sorry
```

```lean
theorem dummy {G : Type*} [Group G] {x : G} {n : ℕ} (hn : 0 < n) (hx : x ^ n = 1) : x⁻¹ = x ^ (n - 1) := sorry
```

## item 39  [pnv-test-239]  set C

**NL.** Prove that every nonzero ideal in the ring of Gauss integers contains a nonzero integer.

```lean
theorem exercise_10_6_7 {I : Ideal GaussianInt}
  (hI : I ≠ ⊥) : ∃ (z : I), z ≠ 0 ∧ (z : GaussianInt).im = 0 := sorry
```

```lean
theorem dummy {R : Type*} [CommRing R] (I : Ideal R) (hI : I ≠ ⊥) : ∃ (x : R), x ≠ 0 ∧ x ∉ I := sorry
```

## item 40  [pnv-test-375]  set C

**NL.** If $\sigma, \tau$ are two permutations that disturb no common element and $\sigma \tau = e$, prove that $\sigma = \tau = e$.

```lean
theorem exercise_3_2_21 {α : Type*} [Fintype α] {σ τ: Equiv.Perm α}
  (h1 : ∀ a : α, σ a = a ↔ τ a ≠ a) (h2 : τ ∘ σ = id) :
  σ = 1 ∧ τ = 1 := sorry
```

```lean
theorem dummy {α : Type*} {σ τ : Equiv.Perm α} (h : ∀ x : α, σ x = τ x) (hστ : σ * τ = 1) : σ = τ := sorry
```

## item 41  [pnv-test-836]  set B

**NL.** Prove that the multiplication of residue class $\mathbb{Z}/n\mathbb{Z}$ is associative.

```lean
theorem exercise_1_1_4 (n : ℕ) (a b c : ZMod n) :
  (a * b) * c = a * (b * c) := sorry
```

```lean
theorem dummy (n : ℕ) (a b c : ℕ) : (a * b) % n * (c % n) % n = a * b * c % n := sorry
```

## item 42  [pnv-test-738]  set A

**NL.** Prove that $\sum 1/k(\log(k))^p$ converges when $p > 1$.

```lean
theorem exercise_3_63a (p : ℝ) (f : ℕ → ℝ) (hp : p > 1)
  (h : f = λ (k : ℕ) => (1 : ℝ) / (k * (log k) ^ p)) :
  ∃ l, Tendsto f atTop (𝓝 l) := sorry
```

```lean
theorem dummy (p : ℝ) (hp : 1 < p) : Summable fun k => 1 / (↑k * (log ↑k) ^ p) := sorry
```

## item 43  [pnv-test-1074]  set C

**NL.** Prove that $f(x) = x^3 + 3x + 2$ is irreducible in $Q[x]$.

```lean
theorem exercise_4_6_2 : Irreducible (X^3 + 3*X + 2 : Polynomial ℚ) := sorry
```

```lean
theorem dummy (f : Polynomial ℚ) (hf : f.degree = 3) (hf0 : f.coeff 0 = 2) (hf1 : f.coeff 1 = 3) (hf2 : f.coeff 2 = 1) : Irreducible f := sorry
```

## item 44  [pnv-test-911]  set C

**NL.** Suppose $T \in \mathcal{L}(V)$ is such that every subspace of $V$ with dimension $\operatorname{dim} V-1$ is invariant under $T$. Prove that $T$ is a scalar multiple of the identity operator.

```lean
theorem exercise_5_13 {F V : Type*} [AddCommGroup V] [Field F]
  [Module F V] [FiniteDimensional F V] {T : End F V}
  (hS : ∀ U : Submodule F V, finrank F U = finrank F V - 1 →
  Submodule.map T U = U) : ∃ c : F, T = c • LinearMap.id := sorry
```

```lean
theorem dummy {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {T : V →ₗ[ℝ] V} (h : ∀ (W : Submodule ℝ V), W < (⊤ : Submodule ℝ V) → LinearMap.range T ≤ W → LinearMap.range T ≤ W.map T) : ∃ a : ℝ, T = a • LinearMap.id := sorry
```

## item 45  [pnv-test-518]  set C

**NL.** Let $f$ be a real function with a continuous third derivative such that $f(x), f^{\prime}(x), f^{\prime \prime}(x), f^{\prime \prime \prime}(x)$ are positive for all $x$. Suppose that $f^{\prime \prime \prime}(x) \leq f(x)$ for all $x$. Show that $f^{\prime}(x)<2 f(x)$ for all $x$.

```lean
theorem exercise_1999_b4 (f : ℝ → ℝ) (hf: ContDiff ℝ 3 f)
  (hf1 : ∀ n ≤ 3, ∀ x : ℝ, iteratedDeriv n f x > 0)
  (hf2 : ∀ x : ℝ, iteratedDeriv 3 f x ≤ f x) :
  ∀ x : ℝ, deriv f x < 2 * f x := sorry
```

```lean
theorem dummy {f : ℝ → ℝ} (hf : ∀ x, 0 < f x) (hf' : ∀ x, 0 < deriv f x) (hf'' : ∀ x, 0 < deriv^[2] f x) (hf''' : ∀ x, 0 < deriv^[3] f x) (h_bound : ∀ x, deriv^[3] f x ≤ f x) : ∀ x, deriv f x < 2 * f x := sorry
```

## item 46  [pnv-test-72]  set B

**NL.** For any two real sequences $\left\{a_{n}\right\},\left\{b_{n}\right\}$, prove that $\limsup _{n \rightarrow \infty}\left(a_{n}+b_{n}\right) \leq \limsup _{n \rightarrow \infty} a_{n}+\limsup _{n \rightarrow \infty} b_{n},$ provided the sum on the right is not of the form $\infty-\infty$.

```lean
theorem exercise_3_5
    (a b : ℕ → EReal)
    (hareal : ∀ n, a n ≠ ⊤ ∧ a n ≠ ⊥)
    (hbreal : ∀ n, b n ≠ ⊤ ∧ b n ≠ ⊥)
    (ha : limsup a ≠ ⊤)
    (hb : limsup b ≠ ⊥) :
    limsup (λ n => a n + b n) ≤ limsup a + limsup b := sorry
```

```lean
theorem dummy (a b : ℕ → ℝ) : limsup (a + b) ≤ limsup a + limsup b := sorry
```

## item 47  [pnv-test-365]  set A

**NL.** Let $G$ be a finite group which possesses an automorphism $\sigma$ such that $\sigma(g)=g$ if and only if $g=1$. If $\sigma^{2}$ is the identity map from $G$ to $G$, prove that $G$ is abelian.

```lean
theorem exercise_1_6_23 {G : Type*}
  [Group G] (σ : MulAut G) (hs : ∀ g : G, σ g = g ↔ g = 1)
  (hs2 : ∀ g : G, σ (σ g) = g) :
  ∀ x y : G, x*y = y*x := sorry
```

```lean
theorem dummy {G : Type*} [Group G] [Fintype G] (σ : G ≃* G) (hσ : ∀ g : G, σ g = g ↔ g = 1) (hσ2 : ∀ g : G, σ (σ g) = g) : ∀ a b : G, a * b = b * a := sorry
```
