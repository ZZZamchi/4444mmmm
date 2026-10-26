import ExperimentsMathlib.CanonV2

/-!
# Direction goals over the canonical components

For the canonical telescopes of `R` and `S` (same alignment as `CanonV2.goals`):

* `pimp`  `∀ x̄, (H_R → C_R) ↔ (H_S → C_S)`: the pointwise claims agree, so a reject of the
  pair is vacuity-only (`T6.vacuity_only_reject`);
* `rs`    `∀ x̄, (H_R → C_R) → (H_S → C_S)`: `S` claims at most what `R` claims at each point,
  hence `Cl R → Cl S` (`T6.closed_of_ptLe`);
* `sr`    the converse direction;
* `npimp` the negation of `pimp`: the pointwise claims differ at some point.

`canon2_dir_prove name (R) (S) goal := proof` adds a theorem whose type is the named goal.
-/

open Lean Meta Elab Command Term

namespace CanonV2

def dirGoals (R S : Expr) : MetaM (Array (Name × Expr)) :=
  withCanon R fun rt => withCanon S fun st => do
    let rHyp ← rt.types.mapM isProp
    let sHyp ← st.types.mapM isProp
    let (cutR, cutS, src, dst, _) ← matchCut rt st rHyp sHyp (depCut rt rHyp) (depCut st sHyp)
    let (xs, tys, rh, rc, _) ← split rt rHyp cutR
    let (_, _, sh, sc, _) ← split st sHyp cutS
    let hr := conj rh
    let hs := (conj sh).replaceFVars src dst
    let cs := sc.replaceFVars src dst
    let pr ← mkArrow hr rc
    let ps ← mkArrow hs cs
    let all (b : Expr) := close xs tys b
    return #[(`pimp, ← all (mkIff pr ps)), (`npimp, mkNot (← all (mkIff pr ps))),
      (`rs, ← all (← mkArrow pr ps)), (`sr, ← all (← mkArrow ps pr))]

syntax (name := canon2DirGoals) "#canon2_dir_goals " str " (" term ")" " (" term ")" : command

elab_rules : command
  | `(#canon2_dir_goals $tag ($r) ($s)) => liftTermElabM do
    let tag := tag.getString
    try
      let gs ← dirGoals (← elabProp r) (← elabProp s)
      let mut msg := m!"CANON_BEGIN {tag}\nCANON_INFO dir"
      for (n, g) in gs do
        msg := msg ++ m!"\nCANON_GOAL {n} ::: {g}"
      logInfo (msg ++ m!"\nCANON_END {tag}")
    catch e =>
      logInfo m!"CANON_BEGIN {tag}\nCANON_FAIL {e.toMessageData}\nCANON_END {tag}"

syntax (name := canon2DirProve) "canon2_dir_prove " ident " (" term ")" " (" term ")" ident " := " term : command

elab_rules : command
  | `(canon2_dir_prove $n:ident ($r) ($s) $g:ident := $pf) => liftTermElabM do
    let gs ← dirGoals (← elabProp r) (← elabProp s)
    let some (_, goal) := gs.find? (·.1 == g.getId) | throwError "unknown goal {g.getId}"
    let v ← elabTermEnsuringType pf goal
    synthesizeSyntheticMVarsNoPostponing
    let v ← instantiateMVars v
    if v.hasMVar then throwError "proof has metavariables"
    if v.hasSorry then logWarning "declaration uses 'sorry'"
    let lps := (collectLevelParams (collectLevelParams {} goal) v).params.toList
    addDecl <| .thmDecl { name := (← getCurrNamespace) ++ n.getId, levelParams := lps, type := goal, value := v }

end CanonV2
