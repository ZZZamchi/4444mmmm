import Lean

/-!
# Canonical telescopes with switchable rules

`CanonV2` with each rewriting rule behind a flag, for measuring how verdicts depend on the
rules. The flag string is a comma-separated subset of

* `nonotex`   do not read `¬ ∃ x, P` as `∀ x, ¬ P`,
* `nobot`     do not read a final `P → False` as `¬ P`,
* `noonept`   do not eliminate one-point binders `x = t`,
* `nohoist`   do not hoist hypotheses after the dependency cut into `H`,
* `onept2`    eliminate a one-point binder `x = t` also when binders between `x` and the
  equation mention `x`, provided every variable of `t` is bound before each of them.

With the empty string the goals are those of `CanonV2`.
`#canon2v_goals "tag" "flags" (R) (S)` prints the goals;
`canon2v_prove "flags" n (R) (S) g := proof` checks `proof` against goal `g`.
-/

open Lean Meta Elab Command Term

namespace CanonV2Var

structure Flags where
  notEx : Bool := true
  bot : Bool := true
  onePt : Bool := true
  hoist : Bool := true
  onePt2 : Bool := false

def Flags.parse (s : String) : Flags :=
  let ws := s.splitOn ","
  { notEx := !ws.contains "nonotex", bot := !ws.contains "nobot",
    onePt := !ws.contains "noonept", hoist := !ws.contains "nohoist", onePt2 := ws.contains "onept2" }

structure Tel where
  fvars : Array Expr
  types : Array Expr
  body : Expr

def close (xs types : Array Expr) (body : Expr) : MetaM Expr := do
  let mut r := body
  for i in (List.range xs.size).reverse do
    let x := xs[i]!
    let d ← x.fvarId!.getDecl
    r := .forallE d.userName types[i]! (r.abstract #[x]) d.binderInfo
  return r

partial def peel {α} (f : Flags) (e : Expr) (xs : Array Expr) (k : Array Expr → Expr → MetaM α) :
    MetaM α := do
  let e := e.consumeMData
  if let .forallE n t b bi := e then
    return ← withLocalDecl n bi t fun x => peel f (b.instantiate1 x) (xs.push x) k
  if f.notEx && e.isAppOfArity ``Not 1 then
    let p := e.appArg!.consumeMData
    if p.isAppOfArity ``Exists 2 then
      if let .lam n t b _ := p.appArg!.consumeMData then
        return ← withLocalDecl n .default t fun x => peel f (mkNot (b.instantiate1 x)) (xs.push x) k
  k xs e

def isData (x ty : Expr) : MetaM Bool := do
  let d ← x.fvarId!.getDecl
  return !(← isProp ty) && !d.binderInfo.isInstImplicit

partial def onePoint (relaxed : Bool) (t : Tel) : MetaM Tel := do
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
      let ok ← if relaxed then
          -- every variable of `s` must be bound before each binder that mentions `x`
          let last := (List.range t.fvars.size).foldl
            (fun m i => if s.containsFVar t.fvars[i]!.fvarId! then i else m) 0
          pure !((List.range t.fvars.size).any fun i =>
            i > k && i != j && i ≤ last && t.types[i]!.containsFVar x.fvarId!)
        else do
          let blocked := (List.range t.fvars.size).any fun i =>
            i > k && i < j && t.types[i]!.containsFVar x.fvarId!
          let dataDep ← (List.range t.fvars.size).anyM fun i => do
            return i > k && t.types[i]!.containsFVar x.fvarId! && !(← isProp t.types[i]!)
          pure !(blocked || dataDep)
      unless ok do continue
      let idx := (List.range t.fvars.size).filter (fun i => i != j && i != k)
      return ← onePoint relaxed {
        fvars := idx.toArray.map (t.fvars[·]!)
        types := idx.toArray.map fun i => t.types[i]!.replaceFVar x s
        body := t.body.replaceFVar x s }
  return t

def isBot (e : Expr) : Bool :=
  e.isConstOf ``False ||
    (e.isAppOfArity ``Eq 3 && (e.getArg! 1).isConstOf ``Bool.false && (e.getArg! 2).isConstOf ``Bool.true)

def unpeelBot (t : Tel) : MetaM Tel := do
  let n := t.fvars.size
  unless n > 0 && isBot t.body.consumeMData do return t
  let ty := t.types[n - 1]!
  unless ← isProp ty do return t
  return { fvars := t.fvars.pop, types := t.types.pop, body := mkNot ty }

def withCanon {α} (f : Flags) (e : Expr) (k : Tel → MetaM α) : MetaM α :=
  peel f e #[] fun xs body => do
    let t : Tel := { fvars := xs, types := ← xs.mapM inferType, body }
    let t ← if f.bot then unpeelBot t else pure t
    k (← if f.onePt then onePoint f.onePt2 t else pure t)

def depCut (t : Tel) (hyp : Array Bool) : Nat := Id.run do
  for i in [:t.fvars.size] do
    if hyp[i]! then
      let id := t.fvars[i]!.fvarId!
      if t.body.containsFVar id || ((t.types.extract (i + 1) t.types.size).any (·.containsFVar id)) then
        return i
  return t.fvars.size

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

def hoistable (t : Tel) (hyp : Array Bool) (cut : Nat) : Array Nat := Id.run do
  let n := t.fvars.size
  let mut out := #[]
  for i in [cut:n] do
    unless hyp[i]! do continue
    let id := t.fvars[i]!.fvarId!
    let early := (List.range i).any fun j => j ≥ cut && t.types[i]!.containsFVar t.fvars[j]!.fvarId!
    let used := t.body.containsFVar id || (List.range n).any fun j => j > i && t.types[j]!.containsFVar id
    unless early || used do out := out.push i
  return out

def split (f : Flags) (t : Tel) (hyp : Array Bool) (cut : Nat) :
    MetaM (Array Expr × Array Expr × Array Expr × Expr × Nat) := do
  let mut xs := #[]
  let mut tys := #[]
  let mut hs := #[]
  for i in [:cut] do
    if hyp[i]! then hs := hs.push t.types[i]!
    else
      xs := xs.push t.fvars[i]!
      tys := tys.push t.types[i]!
  let hoist := if f.hoist then hoistable t hyp cut else #[]
  for i in hoist do hs := hs.push t.types[i]!
  let keep := ((List.range t.fvars.size).filter fun i => i ≥ cut && !hoist.contains i).toArray
  let c ← close (keep.map (t.fvars[·]!)) (keep.map (t.types[·]!)) t.body
  return (xs, tys, hs, c, hoist.size)

def goals (f : Flags) (R S : Expr) : MetaM (Array (Name × Expr) × String) :=
  withCanon f R fun rt => withCanon f S fun st => do
    let rHyp ← rt.types.mapM isProp
    let sHyp ← st.types.mapM isProp
    let (cutR, cutS, src, dst, ambiguous) ← matchCut rt st rHyp sHyp (depCut rt rHyp) (depCut st sHyp)
    let (xs, tys, rh, rc, hoR) ← split f rt rHyp cutR
    let (sxs, stys, sh, sc, hoS) ← split f st sHyp cutS
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
      s!"prefix_s={cutS}/{st.fvars.size} shared={xs.size} hoist_r={hoR} hoist_s={hoS}"
    return (out, info)

def elabProp (stx : Term) : TermElabM Expr := do
  let e ← elabType stx
  synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  if e.hasMVar then throwError "CANON_FAIL metavariables in statement"
  return e

syntax (name := canon2vGoals) "#canon2v_goals " str str " (" term ")" " (" term ")" : command
syntax (name := canon2vProve) "canon2v_prove " str ident " (" term ")" " (" term ")" ident " := " term : command

elab_rules : command
  | `(#canon2v_goals $tag $fl ($r) ($s)) => liftTermElabM do
    let tag := tag.getString
    try
      let (gs, info) ← goals (Flags.parse fl.getString) (← elabProp r) (← elabProp s)
      let mut msg := m!"CANON_BEGIN {tag}\nCANON_INFO {info}"
      for (n, g) in gs do
        msg := msg ++ m!"\nCANON_GOAL {n} ::: {g}"
      logInfo (msg ++ m!"\nCANON_END {tag}")
    catch e =>
      logInfo m!"CANON_BEGIN {tag}\nCANON_FAIL {e.toMessageData}\nCANON_END {tag}"

elab_rules : command
  | `(canon2v_prove $fl $n:ident ($r) ($s) $g:ident := $pf) => liftTermElabM do
    let (gs, _) ← goals (Flags.parse fl.getString) (← elabProp r) (← elabProp s)
    let some (_, goal) := gs.find? (·.1 == g.getId) | throwError "unknown goal {g.getId}"
    let v ← elabTermEnsuringType pf goal
    synthesizeSyntheticMVarsNoPostponing
    let v ← instantiateMVars v
    if v.hasMVar then throwError "proof has metavariables"
    if v.hasSorry then logWarning "declaration uses 'sorry'"
    let lps := (collectLevelParams (collectLevelParams {} goal) v).params.toList
    addDecl <| .thmDecl { name := (← getCurrNamespace) ++ n.getId, levelParams := lps, type := goal, value := v }

end CanonV2Var
