import Mathlib

/-!
# T1 指纹坍缩与「定义域外」原理

1. `fingerprint_collapse`：Faithfulness Gap（arXiv 2606.16541）Def. 3.1 的双向可证指纹
   只依赖语句的可证等价类；任意两条可证语句在任何探针集上指纹相同。
2. 条件外延不可能性：比较「同一假设下结论是否等价」的任何等价关系，
   会把同一假设下的所有真定理识别为一类（`condExt_collapse`）。
3. 该文附录 A 的动机例子：极值定理 (A) 与量词倒置 (C) 都可证，
   因此 BPF 指纹相同、条件等价成立，只有定义域外（`K = ∅`）的组件比较能区分。
-/

namespace T1

/-! ## 1. 双向可证指纹 -/

/-- 探针 `P` 在 `F` 的前向指纹中：`F → P`。 -/
def Fwd (F P : Prop) : Prop := F → P

/-- 探针 `P` 在 `F` 的后向指纹中：`P → F`。 -/
def Bwd (F P : Prop) : Prop := P → F

/-- 两条语句在探针族 `probe` 上的前后向指纹逐项一致。 -/
def SameFingerprint {ι : Sort*} (probe : ι → Prop) (F G : Prop) : Prop :=
  ∀ i, (Fwd F (probe i) ↔ Fwd G (probe i)) ∧ (Bwd F (probe i) ↔ Bwd G (probe i))

theorem fingerprint_of_iff {ι : Sort*} (probe : ι → Prop) {F G : Prop} (h : F ↔ G) :
    SameFingerprint probe F G :=
  fun _ => ⟨⟨fun f g => f (h.2 g), fun g f => g (h.1 f)⟩,
            ⟨fun f p => h.1 (f p), fun g p => h.2 (g p)⟩⟩

/-- 任意两条可证语句在任何探针集上指纹相同。 -/
theorem fingerprint_collapse {ι : Sort*} (probe : ι → Prop) {F G : Prop} (hF : F) (hG : G) :
    SameFingerprint probe F G :=
  fingerprint_of_iff probe ⟨fun _ => hG, fun _ => hF⟩

/-- 可证语句的后向指纹是全部探针。 -/
theorem bwd_full {F : Prop} (hF : F) (P : Prop) : Bwd F P := fun _ => hF

/-! ## 2. 望远镜语句与三种比较 -/

/-- 共享语境 `α` 上的语句 `∀ x, H x → C x`。 -/
structure Stmt (α : Sort*) where
  H : α → Prop
  C : α → Prop

variable {α : Sort*}

def Stmt.Closed (S : Stmt α) : Prop := ∀ x, S.H x → S.C x

/-- 条件等价：假设逐点等价，结论在假设成立处逐点等价。 -/
def CondEquiv (R S : Stmt α) : Prop :=
  ∀ x, (R.H x ↔ S.H x) ∧ (R.H x → (R.C x ↔ S.C x))

/-- 组件等价：假设与结论都逐点无条件等价。 -/
def CompEquiv (R S : Stmt α) : Prop :=
  ∀ x, (R.H x ↔ S.H x) ∧ (R.C x ↔ S.C x)

theorem CompEquiv.cond {R S : Stmt α} (h : CompEquiv R S) : CondEquiv R S :=
  fun x => ⟨(h x).1, fun _ => (h x).2⟩

theorem CondEquiv.closed {R S : Stmt α} (h : CondEquiv R S) : R.Closed ↔ S.Closed :=
  ⟨fun r x hx => ((h x).2 ((h x).1.2 hx)).1 (r x ((h x).1.2 hx)),
   fun s x hx => ((h x).2 hx).2 (s x ((h x).1.1 hx))⟩

/-- 同一假设下的两条真定理总是条件等价。 -/
theorem cond_collapse {H C C' : α → Prop} (hC : ∀ x, H x → C x) (hC' : ∀ x, H x → C' x) :
    CondEquiv ⟨H, C⟩ ⟨H, C'⟩ :=
  fun x => ⟨Iff.rfl, fun hx => ⟨fun _ => hC' x hx, fun _ => hC x hx⟩⟩

/-- 条件外延：结论在假设成立处逐点等价时，关系 `r` 认为两条语句相同。 -/
def CondExt (H : α → Prop) (r : (α → Prop) → (α → Prop) → Prop) : Prop :=
  ∀ C C', (∀ x, H x → (C x ↔ C' x)) → r C C'

/-- 不可能性：满足条件外延的任何等价关系，把假设 `H` 下的所有真定理识别为一类。 -/
theorem condExt_collapse {H : α → Prop} {r : (α → Prop) → (α → Prop) → Prop}
    (hr : Equivalence r) (hext : CondExt H r) {C C' : α → Prop}
    (hC : ∀ x, H x → C x) (hC' : ∀ x, H x → C' x) : r C C' :=
  hr.trans (hext C (fun _ => True) fun x hx => ⟨fun _ => trivial, fun _ => hC x hx⟩)
    (hext (fun _ => True) C' fun x hx => ⟨fun _ => hC' x hx, fun _ => trivial⟩)

/-- 区分两条同假设真定理的唯一途径是比较假设之外的结论：
条件等价而组件不等价时，分歧点一定在假设之外。 -/
theorem offDomain_witness {R S : Stmt α} (hc : CondEquiv R S) {x : α}
    (hx : ¬ (R.C x ↔ S.C x)) : ¬ R.H x :=
  fun h => hx ((hc x).2 h)

/-- 守卫等价：结论只在守卫 `D` 内比较。`D` 取结论中部分运算的定义域时，
对 Lean 默认值（`x / 0 = 0`、`0 - 1 = 0`）不敏感。 -/
def GuardEquiv (D : α → Prop) (R S : Stmt α) : Prop :=
  ∀ x, (R.H x ↔ S.H x) ∧ (D x → (R.C x ↔ S.C x))

theorem CompEquiv.guard {R S : Stmt α} (D : α → Prop) (h : CompEquiv R S) :
    GuardEquiv D R S :=
  fun x => ⟨(h x).1, fun _ => (h x).2⟩

/-- 守卫落在假设之内时，守卫等价退化为条件等价，坍缩重新出现。 -/
theorem guard_collapse_of_sub {D H C C' : α → Prop} (hD : ∀ x, D x → H x)
    (hC : ∀ x, H x → C x) (hC' : ∀ x, H x → C' x) :
    GuardEquiv D ⟨H, C⟩ ⟨H, C'⟩ :=
  fun x => ⟨Iff.rfl, fun hx => ⟨fun _ => hC' x (hD x hx), fun _ => hC x (hD x hx)⟩⟩

/-- 守卫内、假设外的一个分歧点即可反驳守卫等价。 -/
theorem guard_refute {D : α → Prop} {R S : Stmt α} (x : α) (hx : D x)
    (hne : ¬ (R.C x ↔ S.C x)) : ¬ GuardEquiv D R S :=
  fun h => hne ((h x).2 hx)

/-! ## 3. Faithfulness Gap 附录 A 的极值定理例子 -/

/-- 语境：紧集 `K` 与函数 `f`。 -/
abbrev EvtCtx := Set ℝ × (ℝ → ℝ)

def evtH : EvtCtx → Prop := fun p => IsCompact p.1 ∧ p.1.Nonempty ∧ ContinuousOn p.2 p.1

/-- (A) 忠实：`∃ x ∈ K, ∀ y ∈ K, f y ≤ f x`。 -/
def evtA : Stmt EvtCtx := ⟨evtH, fun p => ∃ x ∈ p.1, ∀ y ∈ p.1, p.2 y ≤ p.2 x⟩

/-- (C) 量词倒置：`∀ y ∈ K, ∃ x ∈ K, f y ≤ f x`。 -/
def evtC : Stmt EvtCtx := ⟨evtH, fun p => ∀ y ∈ p.1, ∃ x ∈ p.1, p.2 y ≤ p.2 x⟩

theorem evtA_holds : evtA.Closed := by
  rintro ⟨K, f⟩ ⟨hK, hne, hf⟩
  obtain ⟨x, hx, hmax⟩ := hK.exists_isMaxOn hne hf
  exact ⟨x, hx, fun y hy => hmax hy⟩

theorem evtC_holds : evtC.Closed := fun _ _ y hy => ⟨y, hy, le_rfl⟩

/-- (A) 与 (C) 的 BPF 指纹在任何探针集上相同。 -/
theorem evt_same_fingerprint {ι : Sort*} (probe : ι → Prop) :
    SameFingerprint probe evtA.Closed evtC.Closed :=
  fingerprint_collapse probe evtA_holds evtC_holds

theorem evt_cond_equiv : CondEquiv evtA evtC :=
  cond_collapse evtA_holds evtC_holds

/-- 组件比较在 `K = ∅` 处区分二者：(A) 的结论为假，(C) 的结论空真。 -/
theorem evt_not_comp : ¬ CompEquiv evtA evtC := by
  intro h
  have := ((h (∅, id)).2).2 (fun y hy => absurd hy (Set.notMem_empty y))
  obtain ⟨x, hx, -⟩ := this
  exact Set.notMem_empty x hx

/-- 极值定理的结论不含部分运算，守卫取全体；守卫等价仍能区分 (A) 与 (C)。 -/
theorem evt_not_guard : ¬ GuardEquiv (fun _ => True) evtA evtC :=
  guard_refute (∅, id) trivial fun h => by
    obtain ⟨x, hx, -⟩ := h.2 fun y hy => absurd hy (Set.notMem_empty y)
    exact Set.notMem_empty x hx

/-- Faithfulness Gap 的 ε-忠实（Def. 3.2）以可证等价定义：
(A) 在解释分布的支撑中时，(C) 与 (A) 可证等价，因此按该文自己的定义 (C) 是忠实的。 -/
theorem evt_C_faithful_by_BPF_def : evtA.Closed ↔ evtC.Closed :=
  ⟨fun _ => evtC_holds, fun _ => evtA_holds⟩

end T1
