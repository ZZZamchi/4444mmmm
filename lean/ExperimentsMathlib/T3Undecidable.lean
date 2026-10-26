import Mathlib

/-!
# T3 组件比较的不可判定性与「未知」的位置

对每个程序编码 `c`，构造共享语境 `ℕ` 上的一对语句：
参考的结论为「`c` 在输入 0 上前 `k` 步未停机」，候选的结论为 `True`，假设都为 `True`。
组件都是可判定的（有界步数求值），且

* `comp_iff`：组件等价 ⟺ `c` 在 0 上不停机；
* `not_computable`：组件等价不是可计算谓词；
* `not_equiv_re`：组件不等价是递归可枚举的（反驳半可判定）；
* `sound_checker_has_unknown`：任何可靠且可计算的三值判定器都有输出「未知」的输入。

因此在可判定组件上，「未知」只可能落在接受一侧；反驳一侧可以用有限实例完备地搜索。
-/

namespace T3
open Nat.Partrec

/-- 与 `T1.Stmt` 相同：共享语境 `α` 上的语句 `∀ x, H x → C x`。 -/
structure Stmt (α : Sort*) where
  H : α → Prop
  C : α → Prop

def CompEquiv {α : Sort*} (R S : Stmt α) : Prop :=
  ∀ x, (R.H x ↔ S.H x) ∧ (R.C x ↔ S.C x)

/-- 参考：结论为「前 `k` 步未停机」。 -/
def ref (c : Code) : Stmt ℕ := ⟨fun _ => True, fun k => Code.evaln k c 0 = Option.none⟩

/-- 候选：结论恒真。 -/
def cand : Stmt ℕ := ⟨fun _ => True, fun _ => True⟩

theorem comp_iff (c : Code) : CompEquiv (ref c) cand ↔ ¬ (Code.eval c 0).Dom := by
  constructor
  · intro h hd
    obtain ⟨k, hk⟩ := Code.evaln_complete.1 (Part.get_mem hd)
    have hnone : Code.evaln k c 0 = Option.none := ((h k).2).2 trivial
    rw [hnone] at hk
    exact Option.not_mem_none _ hk
  · intro hnd k
    refine ⟨Iff.rfl, ⟨fun _ => trivial, fun _ => ?_⟩⟩
    show Code.evaln k c 0 = Option.none
    cases hv : Code.evaln k c 0 with
    | none => rfl
    | some x =>
      exact absurd (Part.dom_iff_mem.2 ⟨x, Code.evaln_sound (Option.mem_def.2 hv)⟩) hnd

theorem not_computable : ¬ ComputablePred fun c => CompEquiv (ref c) cand := by
  intro h
  have h' : ComputablePred fun c => ¬ (Code.eval c 0).Dom :=
    (funext fun c => propext (comp_iff c)) ▸ h
  exact ComputablePred.halting_problem 0 (by simpa using h'.not)

theorem not_equiv_re : REPred fun c => ¬ CompEquiv (ref c) cand := by
  have : (fun c => ¬ CompEquiv (ref c) cand) = fun c => (Code.eval c 0).Dom :=
    funext fun c => propext (by rw [comp_iff, not_not])
  rw [this]
  exact ComputablePred.halting_problem_re 0

/-- 可靠的三值判定器：`acc` 为真则等价，`rej` 为真则不等价。
若两者都可计算，则必有两者同时为假（输出「未知」）的输入。 -/
theorem sound_checker_has_unknown (acc rej : Code → Bool)
    (hacc : Computable acc) (sacc : ∀ c, acc c = true → CompEquiv (ref c) cand)
    (srej : ∀ c, rej c = true → ¬ CompEquiv (ref c) cand) :
    ∃ c, acc c = false ∧ rej c = false := by
  by_contra hall
  push_neg at hall
  refine not_computable (ComputablePred.computable_iff.2 ⟨acc, hacc, funext fun c => ?_⟩)
  apply propext
  constructor
  · intro he
    cases ha : acc c with
    | true => rfl
    | false => exact absurd he (srej c (by simpa using hall c ha))
  · intro ha
    exact sacc c ha

end T3
