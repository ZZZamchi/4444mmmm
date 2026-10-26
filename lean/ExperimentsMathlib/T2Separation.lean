import Mathlib

/-!
# T2 反驳难度的分离

参考语句 `R` 为真时：

1. `refute_dir_proves`：反驳一个方向 `R → S` 本身就给出 `R` 的证明。
2. `refute_iff_proves`：若 `S` 可被反驳，反驳闭合等价 `R ↔ S` 恰好等价于证明 `R`。
3. 组件级反驳只需要一个落在假设内的实例，与 `R` 的证明无关。

例子：参考为 Fermat 大定理，翻译把结论 `a^n + b^n ≠ c^n` 写成 `a^n + b^n ≠ c^n + 1`。
闭合层面反驳等价等于证明 Fermat 大定理（`flt_refute_iff`）；
组件层面用 Ramanujan 的 `9^3 + 10^3 = 12^3 + 1` 一步反驳（`flt_drift_not_cond`）。
-/

namespace T2

/-- 与 `T1.Stmt` 相同：共享语境 `α` 上的语句 `∀ x, H x → C x`。 -/
structure Stmt (α : Sort*) where
  H : α → Prop
  C : α → Prop

def Stmt.Closed {α : Sort*} (S : Stmt α) : Prop := ∀ x, S.H x → S.C x

def CondEquiv {α : Sort*} (R S : Stmt α) : Prop :=
  ∀ x, (R.H x ↔ S.H x) ∧ (R.H x → (R.C x ↔ S.C x))

theorem refute_dir_proves {R S : Prop} (h : ¬ (R → S)) : R :=
  Classical.byContradiction fun hR => h fun r => absurd r hR

theorem refute_iff_proves {R S : Prop} (hS : ¬ S) : ¬ (R ↔ S) ↔ R :=
  ⟨fun h => Classical.byContradiction fun hR => h ⟨fun r => absurd r hR, fun s => absurd s hS⟩,
   fun hR h => hS (h.1 hR)⟩

/-- 组件级反驳：假设内的一个实例上结论不等价。 -/
theorem cond_refute {α : Sort*} {R S : Stmt α} (x : α) (hx : R.H x)
    (hne : ¬ (R.C x ↔ S.C x)) : ¬ CondEquiv R S :=
  fun h => hne ((h x).2 hx)

abbrev FltCtx := ℕ × ℕ × ℕ × ℕ

def fltH : FltCtx → Prop := fun ⟨a, b, c, n⟩ => 0 < a ∧ 0 < b ∧ 0 < c ∧ 2 < n

def flt : Stmt FltCtx := ⟨fltH, fun ⟨a, b, c, n⟩ => a ^ n + b ^ n ≠ c ^ n⟩

def fltDrift : Stmt FltCtx := ⟨fltH, fun ⟨a, b, c, n⟩ => a ^ n + b ^ n ≠ c ^ n + 1⟩

theorem taxicab_H : fltH (9, 10, 12, 3) := by
  show 0 < 9 ∧ 0 < 10 ∧ 0 < 12 ∧ 2 < 3
  decide

theorem fltDrift_false : ¬ fltDrift.Closed := fun h => by
  have : 9 ^ 3 + 10 ^ 3 ≠ 12 ^ 3 + 1 := h (9, 10, 12, 3) taxicab_H
  exact this (by decide)

/-- 闭合层面：反驳 `flt ↔ fltDrift` 当且仅当证明 Fermat 大定理。 -/
theorem flt_refute_iff : ¬ (flt.Closed ↔ fltDrift.Closed) ↔ flt.Closed :=
  refute_iff_proves fltDrift_false

/-- 闭合层面单方向也一样：反驳 `flt → fltDrift` 就证明了 Fermat 大定理。 -/
theorem flt_refute_dir (h : ¬ (flt.Closed → fltDrift.Closed)) : flt.Closed :=
  refute_dir_proves h

/-- 组件层面：一个假设内的实例即可反驳，不需要 Fermat 大定理。 -/
theorem flt_drift_not_cond : ¬ CondEquiv flt fltDrift :=
  cond_refute (9, 10, 12, 3) taxicab_H (by
    show ¬ ((9 ^ 3 + 10 ^ 3 ≠ 12 ^ 3) ↔ (9 ^ 3 + 10 ^ 3 ≠ 12 ^ 3 + 1))
    decide)

end T2
