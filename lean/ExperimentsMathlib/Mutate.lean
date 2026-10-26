import ExperimentsMathlib.CanonV2

/-!
# Drift injection on canonical telescopes

`mutate kind R` builds a candidate `S` from a reference `R` by editing its canonical
telescope `(Γ, H, C)` directly, so the drift class of every pair is known by construction:

* `id`     `S = R`                                   (expected: accept)
* `drop`   remove the last hypothesis `Hᵢ`            (expected: reject, accept if `Hᵢ` is redundant)
* `neg`    replace `C` by `¬ C`                       (expected: reject when `H` is satisfiable)
* `offdom` replace `C` by `C ∨ ¬ Hᵢ`                  (expected: off-domain, accept if `C` holds off `H`)

Reward-hacking candidates, each closed-equivalent to `R` exactly when `R` holds:

* `top`    replace `C` by `True`
* `absorb` add `C` as a last hypothesis               (`S` is the absorption `(Γ, H ∧ C, C)`)
* `vac`    add `False` as a last hypothesis

and two variants that propositional logic does not close but one `simp` step does:

* `topsimp`    replace `C` by `∀ k : ℕ, 0 + k = k`
* `absorbsimp` add `∀ k : ℕ, k = k → C` as a last hypothesis

Besides `CanonV2.goals`, `#mutant_goals` and `mutant_prove` also offer the goals
`closed : R ↔ S` and `cand : S`.

The last hypothesis must be a proposition that neither the conclusion nor a later binder
mentions. `#mutant_goals "tag" kind (R)` prints the `CanonV2.goals R S`;
`mutant_prove n kind (R) g := proof` checks `proof` against goal `g`.
-/

open Lean Meta Elab Command Term

namespace Mutate

def lastHyp (t : CanonV2.Tel) : MetaM (Option Nat) := do
  let n := t.fvars.size
  for i in (List.range n).reverse do
    unless ← isProp t.types[i]! do continue
    let id := t.fvars[i]!.fvarId!
    let used := t.body.containsFVar id || (List.range n).any fun j => j > i && t.types[j]!.containsFVar id
    if used then return none
    return some i
  return none

/-- Propositional binders that neither the conclusion nor a later binder mentions. -/
def freeHyps (t : CanonV2.Tel) : MetaM (Array Nat) := do
  let n := t.fvars.size
  let mut out := #[]
  for i in [:n] do
    unless ← isProp t.types[i]! do continue
    let id := t.fvars[i]!.fvarId!
    unless t.body.containsFVar id || (List.range n).any fun j => j > i && t.types[j]!.containsFVar id do
      out := out.push i
  return out

/-- `dropK` / `offdomK`: the edit of `drop` / `offdom` applied to the `K`-th free hypothesis. -/
def indexed? (kind : Name) : Option (Name × Nat) := do
  let s := kind.toString
  for base in ["drop", "offdom"] do
    if s.startsWith base && s.length > base.length then
      if let some k := (s.drop base.length).toNat? then return (Name.mkSimple base, k)
  none

def mutate (kind : Name) (R : Expr) : MetaM Expr :=
  CanonV2.withCanon R fun t => do
    if kind == `id then return R
    if kind == `top then return ← CanonV2.close t.fvars t.types (mkConst ``True)
    if kind == `absorb then
      return ← withLocalDeclD `habs t.body fun h =>
        CanonV2.close (t.fvars.push h) (t.types.push t.body) t.body
    if kind == `vac then
      return ← withLocalDeclD `hvac (mkConst ``False) fun h =>
        CanonV2.close (t.fvars.push h) (t.types.push (mkConst ``False)) t.body
    if kind == `topsimp then
      let c ← withLocalDeclD `k (mkConst ``Nat) fun k => do
        mkForallFVars #[k] (← mkEq (← mkAppM ``HAdd.hAdd #[mkNatLit 0, k]) k)
      return ← CanonV2.close t.fvars t.types c
    if kind == `absorbsimp then
      let a ← withLocalDeclD `k (mkConst ``Nat) fun k => do
        mkForallFVars #[k] (← mkArrow (← mkEq k k) t.body)
      return ← withLocalDeclD `habs a fun h =>
        CanonV2.close (t.fvars.push h) (t.types.push a) t.body
    let (kind, i) ← match indexed? kind with
      | some (b, k) => do
        let hs ← freeHyps t
        let some i := hs[k]? | throwError "no droppable hypothesis"
        pure (b, i)
      | none => do
        let some i ← lastHyp t | throwError "no droppable hypothesis"
        pure (kind, i)
    match kind with
    | `drop =>
      let keep := ((List.range t.fvars.size).filter (· != i)).toArray
      CanonV2.close (keep.map (t.fvars[·]!)) (keep.map (t.types[·]!)) t.body
    | `neg =>
      let b := t.body.consumeMData
      if b.isAppOfArity ``Exists 2 then throwError "existential conclusion"
      CanonV2.close t.fvars t.types (mkNot t.body)
    | `offdom => CanonV2.close t.fvars t.types (mkOr t.body (mkNot t.types[i]!))
    | k => throwError "unknown mutation {k}"

syntax (name := mutantGoals) "#mutant_goals " str ident " (" term ")" : command
syntax (name := mutantProve) "mutant_prove " ident ident " (" term ")" ident " := " term : command

elab_rules : command
  | `(#mutant_goals $tag $k:ident ($r)) => liftTermElabM do
    let tag := tag.getString
    try
      let R ← CanonV2.elabProp r
      let S ← mutate k.getId R
      let (gs, info) ← CanonV2.goals R S
      let gs := (gs.push (`closed, mkIff R S)).push (`cand, S)
      let mut msg := m!"CANON_BEGIN {tag}\nCANON_INFO {info}\nCANON_MUTANT {S}"
      for (n, g) in gs do
        msg := msg ++ m!"\nCANON_GOAL {n} ::: {g}"
      logInfo (msg ++ m!"\nCANON_END {tag}")
    catch e =>
      logInfo m!"CANON_BEGIN {tag}\nCANON_FAIL {e.toMessageData}\nCANON_END {tag}"

elab_rules : command
  | `(mutant_prove $n:ident $k:ident ($r) $g:ident := $pf) => liftTermElabM do
    let R ← CanonV2.elabProp r
    let S ← mutate k.getId R
    let (gs, _) ← CanonV2.goals R S
    let gs := (gs.push (`closed, mkIff R S)).push (`cand, S)
    let some (_, goal) := gs.find? (·.1 == g.getId) | throwError "unknown goal {g.getId}"
    let v ← elabTermEnsuringType pf goal
    synthesizeSyntheticMVarsNoPostponing
    let v ← instantiateMVars v
    if v.hasMVar then throwError "proof has metavariables"
    if v.hasSorry then logWarning "declaration uses 'sorry'"
    let lps := (collectLevelParams (collectLevelParams {} goal) v).params.toList
    addDecl <| .thmDecl { name := (← getCurrNamespace) ++ n.getId, levelParams := lps, type := goal, value := v }

end Mutate

section test

mutant_prove t_id id (∀ n : Nat, 0 < n → 1 ≤ n) acc := by
  exact fun _ => ⟨Iff.rfl, Iff.rfl⟩

mutant_prove t_off offdom (∀ n : Nat, 0 < n → 1 ≤ n) cond := by
  exact fun n => ⟨Iff.rfl, fun h => by simp [h]⟩

mutant_prove t_off2 offdom (∀ n : Nat, 0 < n → 1 ≤ n) ncomp := by
  intro h
  have := (h 0).2 (Or.inr (by simp))
  simp at this

mutant_prove t_drop drop (∀ n : Nat, 0 < n → 1 ≤ n) nhyp := by
  intro h
  have := (h 0).2 trivial
  simp at this

mutant_prove t_drop0 drop0 (∀ n m : Nat, 0 < n → 0 < m → 1 ≤ n) nhyp := by
  intro h
  have := (h 0 1).2 (by simp)
  simp at this

mutant_prove t_neg neg (∀ n : Nat, 0 < n → 1 ≤ n) ncin := by
  intro h
  have := h 1 (by simp)
  simp at this

mutant_prove t_top top (∀ n : Nat, 0 < n → 1 ≤ n) closed := by
  exact ⟨fun _ _ _ => trivial, fun _ n h => h⟩

mutant_prove t_absorb absorb (∀ n : Nat, 0 < n → 1 ≤ n) closed := by
  exact ⟨fun h n h1 _ => h n h1, fun _ n h => h⟩

mutant_prove t_vac vac (∀ n : Nat, 0 < n → 1 ≤ n) closed := by
  exact ⟨fun _ _ _ f => f.elim, fun _ n h => h⟩

mutant_prove t_absorb_acc absorb (∀ n : Nat, 0 < n → 1 ≤ n) acc := by
  intro n
  exact ⟨⟨fun h => ⟨h, h⟩, fun h => h.1⟩, Iff.rfl⟩

mutant_prove t_vac_cand vac (∀ n : Nat, 0 < n → 1 ≤ n) cand := by
  intros; contradiction

mutant_prove t_topsimp topsimp (∀ n : Nat, 0 < n → 1 ≤ n) cand := by
  intros; simp

mutant_prove t_absorbsimp absorbsimp (∀ n : Nat, 0 < n → 1 ≤ n) cand := by
  intros; simp_all

mutant_prove t_absorbsimp_acc absorbsimp (∀ n : Nat, 0 < n → 1 ≤ n) acc := by
  intro n
  exact ⟨⟨fun h => ⟨h, fun _ _ => h⟩, fun h => h.1⟩, Iff.rfl⟩

end test
