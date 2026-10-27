import ExperimentsMathlib.CanonV2

/-!
# Metamorphic tests of the canonicalizer

`represent kind R` rewrites the *surface* form of a statement `R` without changing its
meaning, before any canonicalization:

* `swapK`    swap the `K`-th pair of adjacent binders `(xᵢ, xᵢ₊₁)` such that the type of `xᵢ₊₁`
             does not mention `xᵢ`;
* `conjK`    replace the `K`-th pair of adjacent propositional binders `Hᵢ → Hᵢ₊₁ →` that
             nothing later mentions by `Hᵢ ∧ Hᵢ₊₁ →`;
* `negpeel`  rewrite a final `¬ C` (or `a ≠ b`) as `C → False`;
* `unconjK`  split the `K`-th binder of type `A ∧ B` that nothing later mentions into two.

`#canon2_meta "tag" kind (R)` prints the `CanonV2.goals R (represent kind R)` together with
both canonicalization reports; `canon2_meta_prove n kind (R) g := proof` checks a proof of
goal `g`. If the canonical form is invariant under the re-presentation, the `acc` goal is
closed by `fun _ => ⟨Iff.rfl, Iff.rfl⟩`, up to the order of conjuncts.
-/

open Lean Meta Elab Command Term

namespace CanonMeta

def indexed? (kind : Name) : Option (String × Nat) := do
  let s := kind.toString
  for base in ["swap", "conj", "unconj"] do
    if s.startsWith base && s.length > base.length then
      if let some k := (s.drop base.length).toNat? then return (base, k)
  none

def usedLater (xs : Array Expr) (body : Expr) (i : Nat) : MetaM Bool := do
  let id := xs[i]!.fvarId!
  if body.containsFVar id then return true
  for j in [i+1:xs.size] do
    if (← inferType xs[j]!).containsFVar id then return true
  return false

def represent (kind : Name) (R : Expr) : MetaM Expr :=
  forallTelescope R fun xs body => do
    if kind == `negpeel then
      let b := body.consumeMData
      if b.isAppOfArity ``Not 1 then
        return ← mkForallFVars xs (← mkArrow (b.getArg! 0) (mkConst ``False))
      if b.isAppOfArity ``Ne 3 then
        let eq ← mkEq (b.getArg! 1) (b.getArg! 2)
        return ← mkForallFVars xs (← mkArrow eq (mkConst ``False))
      throwError "conclusion is not a negation"
    let some (base, k) := indexed? kind | throwError "unknown re-presentation {kind}"
    let n := xs.size
    match base with
    | "swap" =>
      let mut cands : Array Nat := #[]
      for i in [:n] do
        if i + 1 < n then
          let tyNext ← inferType xs[i+1]!
          unless tyNext.containsFVar xs[i]!.fvarId! do cands := cands.push i
      let some i := cands[k]? | throwError "no swappable pair {k}"
      let ys := (xs.toList.take i ++ [xs[i+1]!, xs[i]!] ++ xs.toList.drop (i + 2)).toArray
      mkForallFVars ys body
    | "conj" =>
      let mut cands : Array Nat := #[]
      for i in [:n] do
        if i + 1 < n then
          if (← isProp (← inferType xs[i]!)) && (← isProp (← inferType xs[i+1]!)) then
            unless (← usedLater xs body i) || (← usedLater xs body (i+1)) do cands := cands.push i
      let some i := cands[k]? | throwError "no conjoinable pair {k}"
      let h ← mkAppM ``And #[← inferType xs[i]!, ← inferType xs[i+1]!]
      withLocalDeclD `h h fun hv => do
        let ys := (xs.toList.take i ++ [hv] ++ xs.toList.drop (i + 2)).toArray
        mkForallFVars ys body
    | "unconj" =>
      let mut cands : Array Nat := #[]
      for i in [:n] do
        let ty := (← inferType xs[i]!).consumeMData
        if ty.isAppOfArity ``And 2 then
          unless ← usedLater xs body i do cands := cands.push i
      let some i := cands[k]? | throwError "no splittable hypothesis {k}"
      let ty := (← inferType xs[i]!).consumeMData
      withLocalDeclD `h1 (ty.getArg! 0) fun h1 => withLocalDeclD `h2 (ty.getArg! 1) fun h2 => do
        let ys := (xs.toList.take i ++ [h1, h2] ++ xs.toList.drop (i + 1)).toArray
        mkForallFVars ys body
    | _ => throwError "unknown re-presentation {kind}"

syntax (name := metaGoals) "#canon2_meta " str ident " (" term ")" : command
syntax (name := metaProve) "canon2_meta_prove " ident ident " (" term ")" ident " := " term : command

elab_rules : command
  | `(#canon2_meta $tag $k:ident ($r)) => liftTermElabM do
    let tag := tag.getString
    try
      let R ← CanonV2.elabProp r
      let S ← represent k.getId R
      let (gs, info) ← CanonV2.goals R S
      let mut msg := m!"CANON_BEGIN {tag}\nCANON_INFO {info}\nCANON_MUTANT {S}"
      for (n, g) in gs do
        msg := msg ++ m!"\nCANON_GOAL {n} ::: {g}"
      logInfo (msg ++ m!"\nCANON_END {tag}")
    catch e =>
      logInfo m!"CANON_BEGIN {tag}\nCANON_FAIL {e.toMessageData}\nCANON_END {tag}"

elab_rules : command
  | `(canon2_meta_prove $n:ident $k:ident ($r) $g:ident := $pf) => liftTermElabM do
    let R ← CanonV2.elabProp r
    let (gs, _) ← CanonV2.goals R (← represent k.getId R)
    let some (_, goal) := gs.find? (·.1 == g.getId) | throwError "unknown goal {g.getId}"
    let v ← elabTermEnsuringType pf goal
    synthesizeSyntheticMVarsNoPostponing
    let v ← instantiateMVars v
    if v.hasMVar then throwError "proof has metavariables"
    if v.hasSorry then logWarning "declaration uses 'sorry'"
    let lps := (collectLevelParams (collectLevelParams {} goal) v).params.toList
    addDecl <| .thmDecl { name := (← getCurrNamespace) ++ n.getId, levelParams := lps, type := goal, value := v }

end CanonMeta

section test

#canon2_meta "s0" swap0 (∀ n m : Nat, 0 < n → 0 < m → n + m ≠ 0)
#canon2_meta "c0" conj0 (∀ n m : Nat, 0 < n → 0 < m → n + m ≠ 0)
#canon2_meta "np" negpeel (∀ n m : Nat, 0 < n → 0 < m → n + m ≠ 0)
#canon2_meta "u0" unconj0 (∀ n m : Nat, 0 < n ∧ 0 < m → n + m ≠ 0)

canon2_meta_prove t_swap swap0 (∀ n m : Nat, 0 < n → 0 < m → n + m ≠ 0) acc := by
  intros; exact ⟨Iff.rfl, Iff.rfl⟩

canon2_meta_prove t_conj conj0 (∀ n m : Nat, 0 < n → 0 < m → n + m ≠ 0) acc := by
  intros; exact ⟨Iff.rfl, Iff.rfl⟩

canon2_meta_prove t_neg negpeel (∀ n m : Nat, 0 < n → 0 < m → n + m ≠ 0) acc := by
  intros; exact ⟨Iff.rfl, Iff.rfl⟩

canon2_meta_prove t_unconj unconj0 (∀ n m : Nat, 0 < n ∧ 0 < m → n + m ≠ 0) acc := by
  intros; exact ⟨Iff.rfl, Iff.rfl⟩

end test
