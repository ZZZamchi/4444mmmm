import Lean

/-!
# Canonical telescopes and component goals

For closed propositions `R` and `S`:

* each is put in canonical telescope form: leading `∀`, `→`, `¬ P` (read as `P → False`),
  `a ≠ b` (read as `a = b → False`) and `¬ ∃ x, P` (read as `∀ x, ¬ P`) are peeled;
  binders whose type is a proposition are hypotheses, the others are data binders;
  a hypothesis `x = t` or `t = x`, with `x` a data binder not occurring in `t`, is
  eliminated by substitution (one-point rule);
* data binders of `S` are matched, in order, to data binders of `R` with definitionally
  equal types (instance binders only to instance binders; equal names first, then binder
  order);
* each side is cut at its first unmatched data binder or first hypothesis that later
  binders or the conclusion depend on, iterated to a fixpoint. The matched prefix is the
  shared context: its hypotheses form `H`, and everything after the cut, re-quantified,
  forms `C`. Unmatched material is therefore compared as a closed statement inside `C`;
* the component goals `acc cond nhyp ncin ncomp` and the split checks `split_r split_s`
  are built as kernel expressions.

`#canon_goals "tag" (R) (S)` prints the goals; `canon_prove n (R) (S) g := proof` checks `proof`
against goal `g` and adds it as theorem `n`.
-/

open Lean Meta Elab Command Term

namespace Canon

structure Tel where
  fvars : Array Expr
  types : Array Expr
  body : Expr

/-- `∀ xs, body`, where binder `xs[i]` gets type `types[i]` (which may differ from its
local declaration after substitution). -/
def close (xs types : Array Expr) (body : Expr) : MetaM Expr := do
  let mut r := body
  for i in (List.range xs.size).reverse do
    let x := xs[i]!
    let d ← x.fvarId!.getDecl
    r := .forallE d.userName types[i]! (r.abstract #[x]) d.binderInfo
  return r

def negated? (e : Expr) : Option Expr :=
  if e.isAppOfArity ``Not 1 then some e.appArg!
  else if e.isAppOfArity ``Ne 3 then
    some (mkApp3 (mkConst ``Eq e.getAppFn.constLevels!) (e.getArg! 0) (e.getArg! 1) (e.getArg! 2))
  else none

partial def peel {α} (e : Expr) (xs : Array Expr) (k : Array Expr → Expr → MetaM α) : MetaM α := do
  let e := e.consumeMData
  if let .forallE n t b bi := e then
    return ← withLocalDecl n bi t fun x => peel (b.instantiate1 x) (xs.push x) k
  let some p := negated? e | k xs e
  let p := p.consumeMData
  if p.isAppOfArity ``Exists 2 then
    if let .lam n t b _ := p.appArg!.consumeMData then
      return ← withLocalDecl n .default t fun x => peel (mkNot (b.instantiate1 x)) (xs.push x) k
  withLocalDecl `h .default p fun h => peel (mkConst ``False) (xs.push h) k

def isData (x ty : Expr) : MetaM Bool := do
  let d ← x.fvarId!.getDecl
  return !(← isProp ty) && !d.binderInfo.isInstImplicit

partial def onePoint (t : Tel) : MetaM Tel := do
  for j in [:t.fvars.size] do
    let ty := t.types[j]!
    unless ← isProp ty do continue
    let some (_, a, b) := ty.eq? | continue
    for (x, s) in [(a, b), (b, a)] do
      unless x.isFVar do continue
      let some k := t.fvars.idxOf? x | continue
      unless k < j do continue
      unless ← isData x t.types[k]! do continue
      if s.containsFVar x.fvarId! then continue
      let blocked := (List.range t.fvars.size).any fun i =>
        i > k && i < j && t.types[i]!.containsFVar x.fvarId!
      let dataDep ← (List.range t.fvars.size).anyM fun i => do
        return i > k && t.types[i]!.containsFVar x.fvarId! && !(← isProp t.types[i]!)
      if blocked || dataDep then continue
      let idx := (List.range t.fvars.size).filter (fun i => i != j && i != k)
      return ← onePoint {
        fvars := idx.toArray.map (t.fvars[·]!)
        types := idx.toArray.map fun i => t.types[i]!.replaceFVar x s
        body := t.body.replaceFVar x s }
  return t

def withCanon {α} (e : Expr) (k : Tel → MetaM α) : MetaM α :=
  peel e #[] fun xs body => do
    k (← onePoint { fvars := xs, types := ← xs.mapM inferType, body })

/-- Index of the first hypothesis that a later binder type or the conclusion depends on. -/
def depCut (t : Tel) (hyp : Array Bool) : Nat := Id.run do
  for i in [:t.fvars.size] do
    if hyp[i]! then
      let id := t.fvars[i]!.fvarId!
      if t.body.containsFVar id || ((t.types.extract (i + 1) t.types.size).any (·.containsFVar id)) then
        return i
  return t.fvars.size

/-- Match data binders of `st` before `cutS` to data binders of `rt` before `cutR`, cut both
sides at their first unmatched data binder, and repeat until stable. -/
partial def matchCut (rt st : Tel) (rHyp sHyp : Array Bool) (cutR cutS : Nat) :
    MetaM (Nat × Nat × Array Expr × Array Expr × Bool) := do
  let mut used := Array.replicate rt.fvars.size false
  let mut src : Array Expr := #[]
  let mut dst : Array Expr := #[]
  let mut ambiguous := false
  let mut stopS := cutS
  for j in [:cutS] do
    if sHyp[j]! then continue
    let x := st.fvars[j]!
    let ty := st.types[j]!.replaceFVars src dst
    let dx ← x.fvarId!.getDecl
    let mut cands := #[]
    for i in [:cutR] do
      if rHyp[i]! || used[i]! then continue
      let di ← rt.fvars[i]!.fvarId!.getDecl
      if di.binderInfo.isInstImplicit != dx.binderInfo.isInstImplicit then continue
      if ← isDefEq ty rt.types[i]! then cands := cands.push i
    if cands.size > 1 && !dx.binderInfo.isInstImplicit then ambiguous := true
    let byName ← cands.filterM fun i => return (← rt.fvars[i]!.fvarId!.getDecl).userName == dx.userName
    match byName[0]? <|> cands[0]? with
    | some i =>
      used := used.set! i true
      src := src.push x
      dst := dst.push rt.fvars[i]!
    | none =>
      stopS := j
      break
  let mut stopR := cutR
  for i in [:cutR] do
    if !rHyp[i]! && !used[i]! then
      stopR := i
      break
  if stopR == cutR && stopS == cutS then
    return (cutR, cutS, src, dst, ambiguous)
  matchCut rt st rHyp sHyp stopR stopS

def conj (hs : Array Expr) : Expr :=
  if hs.isEmpty then mkConst ``True else hs.pop.foldr mkAnd hs.back!

/-- Prefix data binders with their types, prefix hypotheses, and the re-quantified rest. -/
def split (t : Tel) (hyp : Array Bool) (cut : Nat) : MetaM (Array Expr × Array Expr × Array Expr × Expr) := do
  let mut xs := #[]
  let mut tys := #[]
  let mut hs := #[]
  for i in [:cut] do
    if hyp[i]! then hs := hs.push t.types[i]!
    else
      xs := xs.push t.fvars[i]!
      tys := tys.push t.types[i]!
  let c ← close (t.fvars.extract cut t.fvars.size) (t.types.extract cut t.types.size) t.body
  return (xs, tys, hs, c)

def goals (R S : Expr) : MetaM (Array (Name × Expr) × String) :=
  withCanon R fun rt => withCanon S fun st => do
    let rHyp ← rt.types.mapM isProp
    let sHyp ← st.types.mapM isProp
    let (cutR, cutS, src, dst, ambiguous) ← matchCut rt st rHyp sHyp (depCut rt rHyp) (depCut st sHyp)
    let (xs, tys, rh, rc) ← split rt rHyp cutR
    let (sxs, stys, sh, sc) ← split st sHyp cutS
    let hr := conj rh
    let hs := (conj sh).replaceFVars src dst
    let cs := sc.replaceFVars src dst
    let all (b : Expr) := close xs tys b
    let out := #[
      (`acc, ← all (mkAnd (mkIff hr hs) (mkIff rc cs))),
      (`cond, ← all (mkAnd (mkIff hr hs) (← mkArrow hr (mkIff rc cs)))),
      (`nhyp, mkNot (← all (mkIff hr hs))),
      (`ncin, mkNot (← all (← mkArrow hr (mkIff rc cs)))),
      (`ncomp, mkNot (← all (mkIff rc cs))),
      (`split_r, mkIff R (← close xs tys (← mkArrow hr rc))),
      (`split_s, mkIff S (← close sxs stys (← mkArrow (conj sh) sc)))]
    let full := cutR == rt.fvars.size && cutS == st.fvars.size
    let info := s!"ambiguous={ambiguous} full={full} prefix_r={cutR}/{rt.fvars.size} " ++
      s!"prefix_s={cutS}/{st.fvars.size} shared={xs.size}"
    return (out, info)

def elabProp (stx : Term) : TermElabM Expr := do
  let e ← elabType stx
  synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  if e.hasMVar then throwError "CANON_FAIL metavariables in statement"
  return e

syntax (name := canonGoals) "#canon_goals " str " (" term ")" " (" term ")" : command
syntax (name := canonProve) "canon_prove " ident " (" term ")" " (" term ")" ident " := " term : command

elab_rules : command
  | `(#canon_goals $tag ($r) ($s)) => liftTermElabM do
    let tag := tag.getString
    try
      let (gs, info) ← goals (← elabProp r) (← elabProp s)
      let mut msg := m!"CANON_BEGIN {tag}\nCANON_INFO {info}"
      for (n, g) in gs do
        msg := msg ++ m!"\nCANON_GOAL {n} ::: {g}"
      logInfo (msg ++ m!"\nCANON_END {tag}")
    catch e =>
      logInfo m!"CANON_BEGIN {tag}\nCANON_FAIL {e.toMessageData}\nCANON_END {tag}"

elab_rules : command
  | `(canon_prove $n:ident ($r) ($s) $g:ident := $pf) => liftTermElabM do
    let (gs, _) ← goals (← elabProp r) (← elabProp s)
    let some (_, goal) := gs.find? (·.1 == g.getId) | throwError "unknown goal {g.getId}"
    let v ← elabTermEnsuringType pf goal
    synthesizeSyntheticMVarsNoPostponing
    let v ← instantiateMVars v
    if v.hasMVar then throwError "proof has metavariables"
    if v.hasSorry then logWarning "declaration uses 'sorry'"
    let lps := (collectLevelParams (collectLevelParams {} goal) v).params.toList
    addDecl <| .thmDecl { name := (← getCurrNamespace) ++ n.getId, levelParams := lps, type := goal, value := v }

end Canon
