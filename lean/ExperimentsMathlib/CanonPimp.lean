import ExperimentsMathlib.CanonV2

/-!
# Pointwise-claim goals on top of `CanonV2`

For the canonical telescopes `(x̄, H_R, C_R)` and `(x̄, H_S, C_S)` computed by `CanonV2.goals`,
the pointwise claims are `H_R → C_R` and `H_S → C_S`. The goals below locate a reject between
the characterization layers of `T6`: `pimp` (pointwise-implication equivalent, so the reject is
a vacuity-only difference), its negation, and the two one-sided directions with negations.
The components are read off the `acc` goal `∀ x̄, (H_R ↔ H_S) ∧ (C_R ↔ C_S)`, so they are the
same expressions the five verdict goals use.
-/

open Lean Meta Elab Command Term

namespace CanonPimp

def pimpGoals (R S : Expr) : MetaM (Array (Name × Expr)) := do
  let (gs, info) ← CanonV2.goals R S
  let some (_, acc) := gs.find? (·.1 == `acc) | throwError "no acc goal"
  let some n := (info.splitOn "shared=")[1]?.bind (·.takeWhile Char.isDigit |>.toNat?)
    | throwError "no shared count"
  forallBoundedTelescope acc (some n) fun xs body => do
    let some (h, c) := body.and? | throwError "acc is not a conjunction"
    let some (hr, hs) := h.iff? | throwError "no hypothesis iff"
    let some (cr, cs) := c.iff? | throwError "no conclusion iff"
    let pr ← mkArrow hr cr
    let ps ← mkArrow hs cs
    let all (b : Expr) := mkForallFVars xs b
    let lrs ← all (← mkArrow pr ps)
    let lsr ← all (← mkArrow ps pr)
    return #[(`pimp, ← all (mkIff pr ps)), (`npimp, mkNot (← all (mkIff pr ps))),
      (`le_rs, lrs), (`le_sr, lsr), (`nle_rs, mkNot lrs), (`nle_sr, mkNot lsr)]

syntax (name := canonPimpProve) "canon_pimp_prove " ident " (" term ")" " (" term ")" ident " := " term : command

elab_rules : command
  | `(canon_pimp_prove $n:ident ($r) ($s) $g:ident := $pf) => liftTermElabM do
    let gs ← pimpGoals (← CanonV2.elabProp r) (← CanonV2.elabProp s)
    let some (_, goal) := gs.find? (·.1 == g.getId) | throwError "unknown goal {g.getId}"
    let v ← elabTermEnsuringType pf goal
    synthesizeSyntheticMVarsNoPostponing
    let v ← instantiateMVars v
    if v.hasMVar then throwError "proof has metavariables"
    if v.hasSorry then logWarning "declaration uses 'sorry'"
    let lps := (collectLevelParams (collectLevelParams {} goal) v).params.toList
    addDecl <| .thmDecl { name := (← getCurrNamespace) ++ n.getId, levelParams := lps, type := goal, value := v }

syntax (name := canonPimpGoals) "#canon_pimp_goals " str " (" term ")" " (" term ")" : command

elab_rules : command
  | `(#canon_pimp_goals $tag ($r) ($s)) => liftTermElabM do
    let tag := tag.getString
    try
      let gs ← pimpGoals (← CanonV2.elabProp r) (← CanonV2.elabProp s)
      let mut msg := m!"CANON_BEGIN {tag}"
      for (n, g) in gs do
        msg := msg ++ m!"\nCANON_GOAL {n} ::: {g}"
      logInfo (msg ++ m!"\nCANON_END {tag}")
    catch e =>
      logInfo m!"CANON_BEGIN {tag}\nCANON_FAIL {e.toMessageData}\nCANON_END {tag}"

end CanonPimp
