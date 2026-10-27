import Lean

/-!
# Canonical telescopes, version 2

Same construction as `ExperimentsMathlib.Canon`, with two changes to where the boundary
between hypotheses and conclusion is drawn:

* a final negation `¬ P` (or `a ≠ b`) stays in the conclusion. Peeling it turns a true
  theorem `∀ x, H x → ¬ Q x` into hypotheses `H ∧ Q` that are nowhere satisfiable, and any
  two such theorems then compare as equivalent. `¬ ∃ x, P` is still read as `∀ x, ¬ P`.
  Symmetrically, a conclusion `False` (or `false = true`) after a last hypothesis `P` is
  read as `¬ P`;
* a hypothesis after the cut that mentions only shared binders, and that nothing later
  depends on, is hoisted into `H` (`∀ y, A → X y` is equivalent to `A → ∀ y, X y`).

`#canon2_goals "tag" (R) (S)` prints the goals; `canon2_prove n (R) (S) g := proof` checks
`proof` against goal `g` and adds it as theorem `n`.
-/

open Lean Meta Elab Command Term

namespace CanonV2

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

partial def peel {α} (e : Expr) (xs : Array Expr) (k : Array Expr → Expr → MetaM α) : MetaM α := do
  let e := e.consumeMData
  if let .forallE n t b bi := e then
    return ← withLocalDecl n bi t fun x => peel (b.instantiate1 x) (xs.push x) k
  if e.isAppOfArity ``Not 1 then
    let p := e.appArg!.consumeMData
    if p.isAppOfArity ``Exists 2 then
      if let .lam n t b _ := p.appArg!.consumeMData then
        return ← withLocalDecl n .default t fun x => peel (mkNot (b.instantiate1 x)) (xs.push x) k
  k xs e

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
      -- `s` may be substituted into a type at position `i` only if every binder `s` mentions
      -- is declared before `i`.
      let blocked := (List.range t.fvars.size).any fun i =>
        i > k && i < j && t.types[i]!.containsFVar x.fvarId! &&
          (List.range t.fvars.size).any fun m => m > i && s.containsFVar t.fvars[m]!.fvarId!
      let dataDep ← (List.range t.fvars.size).anyM fun i => do
        return i > k && t.types[i]!.containsFVar x.fvarId! && !(← isProp t.types[i]!)
      if blocked || dataDep then continue
      let idx := (List.range t.fvars.size).filter (fun i => i != j && i != k)
      return ← onePoint {
        fvars := idx.toArray.map (t.fvars[·]!)
        types := idx.toArray.map fun i => t.types[i]!.replaceFVar x s
        body := t.body.replaceFVar x s }
  return t

def isBot (e : Expr) : Bool :=
  e.isConstOf ``False ||
    (e.isAppOfArity ``Eq 3 && (e.getArg! 1).isConstOf ``Bool.false && (e.getArg! 2).isConstOf ``Bool.true)

/-- A conclusion `False` (or `false = true`) after a last hypothesis `h : P` is read as `¬ P`. -/
def unpeelBot (t : Tel) : MetaM Tel := do
  let n := t.fvars.size
  unless n > 0 && isBot t.body.consumeMData do return t
  let ty := t.types[n - 1]!
  unless ← isProp ty do return t
  return { fvars := t.fvars.pop, types := t.types.pop, body := mkNot ty }

/-- A hypothesis `h : A ∧ B` that nothing depends on is split into two binders `A`, `B`
(curried normal form, so `A ∧ B → X` and `A → B → X` read the same). -/
partial def splitConj {α} (t : Tel) (k : Tel → MetaM α) : MetaM α := do
  let n := t.fvars.size
  for i in [:n] do
    let ty := t.types[i]!.consumeMData
    unless ← isProp ty do continue
    let some (a, b) := ty.and? | continue
    let id := t.fvars[i]!.fvarId!
    if t.body.containsFVar id || t.types.any (·.containsFVar id) then continue
    let d ← id.getDecl
    return ← withLocalDecl (d.userName.appendAfter "₁") d.binderInfo a fun ha =>
      withLocalDecl (d.userName.appendAfter "₂") d.binderInfo b fun hb =>
        splitConj {
          fvars := t.fvars.extract 0 i ++ #[ha, hb] ++ t.fvars.extract (i + 1) n
          types := t.types.extract 0 i ++ #[a, b] ++ t.types.extract (i + 1) n
          body := t.body } k
  k t

def withCanon {α} (e : Expr) (k : Tel → MetaM α) : MetaM α :=
  peel e #[] fun xs body => do
    splitConj { fvars := xs, types := ← xs.mapM inferType, body } fun t => do
      let t ← unpeelBot t
      -- a conclusion `¬ P` produced by `unpeelBot` is peeled again (`¬ ∃ x, P` ↦ `∀ x, ¬ P`)
      peel t.body t.fvars fun xs body => do
        k (← onePoint { fvars := xs, types := ← xs.mapM inferType, body })

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

/-- Hypotheses after `cut` that mention no binder after `cut` and that nothing depends on. -/
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

def split (t : Tel) (hyp : Array Bool) (cut : Nat) :
    MetaM (Array Expr × Array Expr × Array Expr × Expr × Nat) := do
  let mut xs := #[]
  let mut tys := #[]
  let mut hs := #[]
  for i in [:cut] do
    if hyp[i]! then hs := hs.push t.types[i]!
    else
      xs := xs.push t.fvars[i]!
      tys := tys.push t.types[i]!
  let hoist := hoistable t hyp cut
  for i in hoist do hs := hs.push t.types[i]!
  let keep := ((List.range t.fvars.size).filter fun i => i ≥ cut && !hoist.contains i).toArray
  let c ← close (keep.map (t.fvars[·]!)) (keep.map (t.types[·]!)) t.body
  return (xs, tys, hs, c, hoist.size)

def goals (R S : Expr) : MetaM (Array (Name × Expr) × String) :=
  withCanon R fun rt => withCanon S fun st => do
    let rHyp ← rt.types.mapM isProp
    let sHyp ← st.types.mapM isProp
    let (cutR, cutS, src, dst, ambiguous) ← matchCut rt st rHyp sHyp (depCut rt rHyp) (depCut st sHyp)
    let (xs, tys, rh, rc, hoR) ← split rt rHyp cutR
    let (sxs, stys, sh, sc, hoS) ← split st sHyp cutS
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

syntax (name := canon2Goals) "#canon2_goals " str " (" term ")" " (" term ")" : command
syntax (name := canon2Prove) "canon2_prove " ident " (" term ")" " (" term ")" ident " := " term : command

elab_rules : command
  | `(#canon2_goals $tag ($r) ($s)) => liftTermElabM do
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
  | `(canon2_prove $n:ident ($r) ($s) $g:ident := $pf) => liftTermElabM do
    let (gs, _) ← goals (← elabProp r) (← elabProp s)
    let some (_, goal) := gs.find? (·.1 == g.getId) | throwError "unknown goal {g.getId}"
    let v ← elabTermEnsuringType pf goal
    synthesizeSyntheticMVarsNoPostponing
    let v ← instantiateMVars v
    if v.hasMVar then throwError "proof has metavariables"
    if v.hasSorry then logWarning "declaration uses 'sorry'"
    let lps := (collectLevelParams (collectLevelParams {} goal) v).params.toList
    addDecl <| .thmDecl { name := (← getCurrNamespace) ++ n.getId, levelParams := lps, type := goal, value := v }

end CanonV2
