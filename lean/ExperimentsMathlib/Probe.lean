import ExperimentsMathlib.Mutate

/-!
# Hypothesis probes for reference statements

For the `k`-th free hypothesis `Hₖ` of the canonical telescope of `R` (a proposition that
neither the conclusion nor a later binder mentions), with the remaining binders `Γ'`:

* `implied`  `∀ Γ', Hₖ`          the other hypotheses already imply `Hₖ`;
* `nimplied` `¬ ∀ Γ', Hₖ`        some point satisfies the others but not `Hₖ`;
* `idle`     `∀ Γ', ¬ Hₖ → C`    the conclusion holds wherever `Hₖ` fails.

`idle` with `nimplied` means `R` stays true at real points without `Hₖ`: the hypothesis
does no work. `#probe_goals "tag" k (R)` prints the goals; `probe_prove n k (R) g := proof`
checks `proof` against goal `g`.
-/

open Lean Meta Elab Command Term

namespace Probe

def goals (k : Nat) (R : Expr) : MetaM (Array (Name × Expr) × String) :=
  CanonV2.withCanon R fun t => do
    let hs ← Mutate.freeHyps t
    let some i := hs[k]? | throwError "no hypothesis {k}"
    let keep := ((List.range t.fvars.size).filter (· != i)).toArray
    let xs := keep.map (t.fvars[·]!)
    let tys := keep.map (t.types[·]!)
    let h := t.types[i]!
    let implied ← CanonV2.close xs tys h
    let idle ← CanonV2.close xs tys (← mkArrow (mkNot h) t.body)
    return (#[(`implied, implied), (`nimplied, mkNot implied), (`idle, idle)],
      s!"free={hs.size} binders={t.fvars.size}")

syntax (name := probeGoals) "#probe_goals " str num " (" term ")" : command
syntax (name := probeProve) "probe_prove " ident num " (" term ")" ident " := " term : command

elab_rules : command
  | `(#probe_goals $tag $k ($r)) => liftTermElabM do
    let tag := tag.getString
    try
      let (gs, info) ← goals k.getNat (← CanonV2.elabProp r)
      let mut msg := m!"CANON_BEGIN {tag}\nCANON_INFO {info}"
      for (n, g) in gs do
        msg := msg ++ m!"\nCANON_GOAL {n} ::: {g}"
      logInfo (msg ++ m!"\nCANON_END {tag}")
    catch e =>
      logInfo m!"CANON_BEGIN {tag}\nCANON_FAIL {e.toMessageData}\nCANON_END {tag}"

/-- Whole-statement probes, independent of any single hypothesis:

* `vacuous`    `∀ Γ, False`  with every binder kept: the hypotheses are jointly unsatisfiable;
* `nonvac`     its negation, a point satisfying all hypotheses;
* `trivial`    `∀ Γ', C` with all free hypotheses removed: the conclusion holds without them;
* `nontrivial` its negation.

`trivial` is only produced when there is at least one free hypothesis. -/
def globalGoals (R : Expr) : MetaM (Array (Name × Expr) × String) :=
  CanonV2.withCanon R fun t => do
    let hs ← Mutate.freeHyps t
    let vac ← CanonV2.close t.fvars t.types (mkConst ``False)
    let mut gs := #[(`vacuous, vac), (`nonvac, mkNot vac)]
    if hs.size > 0 then
      let keep := ((List.range t.fvars.size).filter (fun i => !hs.contains i)).toArray
      let triv ← CanonV2.close (keep.map (t.fvars[·]!)) (keep.map (t.types[·]!)) t.body
      gs := gs ++ #[(`trivial, triv), (`nontrivial, mkNot triv)]
    return (gs, s!"free={hs.size} binders={t.fvars.size}")

syntax (name := probeGlobalGoals) "#probe_global " str " (" term ")" : command
syntax (name := probeGlobalProve) "probe_global_prove " ident " (" term ")" ident " := " term : command

elab_rules : command
  | `(#probe_global $tag ($r)) => liftTermElabM do
    let tag := tag.getString
    try
      let (gs, info) ← globalGoals (← CanonV2.elabProp r)
      let mut msg := m!"CANON_BEGIN {tag}\nCANON_INFO {info}"
      for (n, g) in gs do
        msg := msg ++ m!"\nCANON_GOAL {n} ::: {g}"
      logInfo (msg ++ m!"\nCANON_END {tag}")
    catch e =>
      logInfo m!"CANON_BEGIN {tag}\nCANON_FAIL {e.toMessageData}\nCANON_END {tag}"

elab_rules : command
  | `(probe_global_prove $n:ident ($r) $g:ident := $pf) => liftTermElabM do
    let (gs, _) ← globalGoals (← CanonV2.elabProp r)
    let some (_, goal) := gs.find? (·.1 == g.getId) | throwError "unknown goal {g.getId}"
    let v ← elabTermEnsuringType pf goal
    synthesizeSyntheticMVarsNoPostponing
    let v ← instantiateMVars v
    if v.hasMVar then throwError "proof has metavariables"
    if v.hasSorry then logWarning "declaration uses 'sorry'"
    let lps := (collectLevelParams (collectLevelParams {} goal) v).params.toList
    addDecl <| .thmDecl { name := (← getCurrNamespace) ++ n.getId, levelParams := lps, type := goal, value := v }

elab_rules : command
  | `(probe_prove $n:ident $k ($r) $g:ident := $pf) => liftTermElabM do
    let (gs, _) ← goals k.getNat (← CanonV2.elabProp r)
    let some (_, goal) := gs.find? (·.1 == g.getId) | throwError "unknown goal {g.getId}"
    let v ← elabTermEnsuringType pf goal
    synthesizeSyntheticMVarsNoPostponing
    let v ← instantiateMVars v
    if v.hasMVar then throwError "proof has metavariables"
    if v.hasSorry then logWarning "declaration uses 'sorry'"
    let lps := (collectLevelParams (collectLevelParams {} goal) v).params.toList
    addDecl <| .thmDecl { name := (← getCurrNamespace) ++ n.getId, levelParams := lps, type := goal, value := v }

end Probe

section test

probe_prove p_idle 0 (∀ n : Nat, 0 < n → 0 ≤ n) idle := by
  intro n _; omega

probe_prove p_nimp 0 (∀ n : Nat, 0 < n → 0 ≤ n) nimplied := by
  intro h; have := h 0; omega

probe_prove p_imp 1 (∀ n : Nat, 1 < n → 0 < n → 0 ≤ n) implied := by
  intro n h; omega

#probe_global "g" (∀ n : Nat, 0 < n → n < 0 → n = 1)

probe_global_prove g_vac (∀ n : Nat, 0 < n → n < 0 → n = 1) vacuous := by
  intro n h1 h2; omega

probe_global_prove g_triv (∀ n : Nat, 0 < n → 0 ≤ n) trivial := by
  intro n; omega

probe_global_prove g_nonvac (∀ n : Nat, 0 < n → 0 ≤ n) nonvac := by
  intro h; exact absurd (h 1 (by omega)) (by simp)

end test
