import ExperimentsMathlib.CanonV2

/-!
# Pointwise-collapse goals over the canonical components

For the canonical telescopes of `R` and `S` (same alignment as `CanonV2.goals`):

* `ptr`  `∀ x̄, C_R`: the conclusion of `R` holds at every aligned point, hypotheses dropped;
* `pts`  `∀ x̄, C_S`: the same for `S`;
* `pfr`, `pfs`  `∀ x̄, ¬ C_R` and `∀ x̄, ¬ C_S`: the conclusion fails at every aligned point;
* `nptr`, `npts`, `npfr`, `npfs` the negations of the four.

Under an `acc` certificate `C_R ↔ C_S` holds at every point. If the conclusions are constant
over the aligned points (all true or all false) this says nothing about either statement, and
`acc` certifies no more than `∀ x̄, H_R ↔ H_S`: the pointwise collapse of Proposition
`prop:residue`, of which the closed comparison of two true or two false statements is the case
of an empty prefix. If the conclusion is refuted to be constant in both ways, the accept is not
of this kind.

`canon2_pt_prove name (R) (S) goal := proof` adds a theorem whose type is the named goal.
-/

open Lean Meta Elab Command Term

namespace CanonV2

def ptGoals (R S : Expr) : MetaM (Array (Name × Expr)) :=
  withCanon R fun rt => withCanon S fun st => do
    let rHyp ← rt.types.mapM isProp
    let sHyp ← st.types.mapM isProp
    let (cutR, cutS, src, dst, _) ← matchCut rt st rHyp sHyp (depCut rt rHyp) (depCut st sHyp)
    let (xs, tys, _, rc, _) ← split rt rHyp cutR
    let (_, _, _, sc, _) ← split st sHyp cutS
    let cs := sc.replaceFVars src dst
    let all (b : Expr) := close xs tys b
    let nrc := mkNot rc
    let ncs := mkNot cs
    return #[(`ptr, ← all rc), (`pts, ← all cs), (`nptr, mkNot (← all rc)), (`npts, mkNot (← all cs)),
      (`pfr, ← all nrc), (`pfs, ← all ncs), (`npfr, mkNot (← all nrc)), (`npfs, mkNot (← all ncs))]

syntax (name := canon2PtGoals) "#canon2_pt_goals " str " (" term ")" " (" term ")" : command

elab_rules : command
  | `(#canon2_pt_goals $tag ($r) ($s)) => liftTermElabM do
    let tag := tag.getString
    try
      let gs ← ptGoals (← elabProp r) (← elabProp s)
      let mut msg := m!"CANON_BEGIN {tag}\nCANON_INFO pt"
      for (n, g) in gs do
        msg := msg ++ m!"\nCANON_GOAL {n} ::: {g}"
      logInfo (msg ++ m!"\nCANON_END {tag}")
    catch e =>
      logInfo m!"CANON_BEGIN {tag}\nCANON_FAIL {e.toMessageData}\nCANON_END {tag}"

syntax (name := canon2PtProve) "canon2_pt_prove " ident " (" term ")" " (" term ")" ident " := " term : command

elab_rules : command
  | `(canon2_pt_prove $n:ident ($r) ($s) $g:ident := $pf) => liftTermElabM do
    let gs ← ptGoals (← elabProp r) (← elabProp s)
    let some (_, goal) := gs.find? (·.1 == g.getId) | throwError "unknown goal {g.getId}"
    let v ← elabTermEnsuringType pf goal
    synthesizeSyntheticMVarsNoPostponing
    let v ← instantiateMVars v
    if v.hasMVar then throwError "proof has metavariables"
    if v.hasSorry then logWarning "declaration uses 'sorry'"
    let lps := (collectLevelParams (collectLevelParams {} goal) v).params.toList
    addDecl <| .thmDecl { name := (← getCurrNamespace) ++ n.getId, levelParams := lps, type := goal, value := v }

end CanonV2
