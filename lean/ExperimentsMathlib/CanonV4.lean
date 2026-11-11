import Lean

/-!
# Canonical telescopes, version 4 (development)

`CanonV2Ext` with two more flags and more diagnostics. The flag string is a comma-separated
subset of the flags of `CanonV2Ext` (`nonotex`, `nobot`, `noonept`, `nohoist`, `onept2`,
`subtype`, `classdec`, `dropunused`, `univ0`, `exhyp`, `nonempty`) and

* `align` align by search instead of greedily: among the type-consistent assignments of the data
  binders, the one that aligns the most binders, then under which the most hypotheses of the two
  sides coincide (up to `>`/`<`, `≥`/`≤`, `≠`/`¬ =` and the orientation of `=`), then with the
  most shared subterms that mention an aligned binder; ties keep the `CanonV2` choice. The
  choice is computed from the two statements before any proof is attempted;
* `anon`  rename every binder of the second statement, for testing that verdicts do not depend
  on the names a candidate uses;
* `univ0m` instantiate every universe parameter with `0`, as `univ0`, but only when the two
  statements do not have the same universe parameters (`Type` against `Type*`);
* `shuffle` reverse, in the leading binders of the second statement, every run of consecutive data
  binders with the same type (`(a b c : ℤ)` becomes `(c b a : ℤ)`). The statement means the same;
  with `anon` this tests that the alignment does not depend on binder order and names.

With the empty string the goals are those of `CanonV2`. The info line adds the number of
assignments compared (`perm`), whether the choice differs from `CanonV2` (`moved`), the position in
the first telescope of the binder each aligned data binder of the second is mapped to (`map`), and
the number of hypotheses left after the cut on each side (`rest_hyp_r`, `rest_hyp_s`).
`#canon4_goals "tag" "flags" (R) (S)` prints the goals;
`canon4_prove "flags" n (R) (S) g := proof` checks `proof` against goal `g`.
-/

open Lean Meta Elab Command Term

namespace CanonV4

structure Flags where
  notEx : Bool := true
  bot : Bool := true
  onePt : Bool := true
  hoist : Bool := true
  onePt2 : Bool := false
  subtype : Bool := false
  classDec : Bool := false
  dropUnused : Bool := false
  univ0 : Bool := false
  exHyp : Bool := false
  nonempty : Bool := false
  perm : Bool := false
  anon : Bool := false
  univ0m : Bool := false
  shuffle : Bool := false

def Flags.parse (s : String) : Flags :=
  let ws := s.splitOn ","
  { notEx := !ws.contains "nonotex", bot := !ws.contains "nobot",
    onePt := !ws.contains "noonept", hoist := !ws.contains "nohoist", onePt2 := ws.contains "onept2",
    subtype := ws.contains "subtype", classDec := ws.contains "classdec",
    dropUnused := ws.contains "dropunused", univ0 := ws.contains "univ0",
    exHyp := ws.contains "exhyp", nonempty := ws.contains "nonempty",
    perm := ws.contains "align", anon := ws.contains "anon", univ0m := ws.contains "univ0m",
    shuffle := ws.contains "shuffle" }

/-- Bijections compared at most; beyond this the `CanonV2` choice is kept. -/
def permCap : Nat := 5040

/-- Instantiate every universe parameter with `0`; the goals are then about this instance. -/
def univZero (e : Expr) : Expr :=
  let ps := (collectLevelParams {} e).params.toList
  e.instantiateLevelParams ps (ps.map fun _ => levelZero)

/-- Rename every binder to `v0`, `v1`, ... (binder names carry no meaning). -/
partial def anonymize (e : Expr) : StateM Nat Expr := do
  match e with
  | .forallE _ t b bi =>
    let k ← modifyGet fun n => (n, n + 1)
    return .forallE (Name.mkSimple s!"v{k}") (← anonymize t) (← anonymize b) bi
  | .lam _ t b bi =>
    let k ← modifyGet fun n => (n, n + 1)
    return .lam (Name.mkSimple s!"v{k}") (← anonymize t) (← anonymize b) bi
  | .app f a => return .app (← anonymize f) (← anonymize a)
  | .mdata m b => return .mdata m (← anonymize b)
  | .letE n t v b nd => return .letE n (← anonymize t) (← anonymize v) (← anonymize b) nd
  | .proj s i b => return .proj s i (← anonymize b)
  | _ => return e

/-- Reverse each run of consecutive leading data binders with the same type. -/
def shuffleRuns (e : Expr) : MetaM Expr :=
  forallTelescope e fun xs body => do
    let tys ← xs.mapM inferType
    let data ← (xs.zip tys).mapM fun (x, ty) => do
      return !(← isProp ty) && !(← x.fvarId!.getDecl).binderInfo.isInstImplicit
    let mut out : Array Expr := #[]
    let mut i := 0
    while i < xs.size do
      let mut j := i + 1
      if data[i]! then
        while j < xs.size && data[j]! && tys[j]! == tys[i]! do j := j + 1
      out := out ++ (xs.extract i j).reverse
      i := j
    mkForallFVars out body

/-- The classical instance for a binder of a `Decidable` class, if it is one. -/
def classicalInst? (ty : Expr) : MetaM (Option Expr) := do
  let ty ← instantiateMVars ty
  let fn := ty.getAppFn
  let some c := fn.constName? | return none
  let args := ty.getAppArgs
  try
    match c, args.size with
    | ``Decidable, 1 => return some (mkApp (mkConst ``Classical.propDecidable) args[0]!)
    | ``DecidableEq, 1 => return some (← mkAppOptM `Classical.decEq #[args[0]!])
    | ``DecidablePred, 2 => return some (← mkAppOptM `Classical.decPred #[args[0]!, args[1]!])
    | ``DecidableRel, 2 => return some (← mkAppOptM `Classical.decRel #[args[0]!, args[1]!])
    | _, _ => return none
  catch _ => return none

/-- `(α, p)` if `ty` unfolds to `Subtype p` (`ℕ+`, coerced sets and subobjects). -/
def subtype? (ty : Expr) : MetaM (Option (Expr × Expr)) := do
  if ← isProp ty then return none
  let ty' ← whnfD ty
  if ty'.isAppOfArity ``Subtype 2 then return some (ty'.getArg! 0, ty'.getArg! 1)
  return none

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

/-- Rewrite applications to `v = ⟨y, h⟩` that reduce to `y` (the coercions `↑⟨y, h⟩`) into `y`. -/
def valToBase (v y e : Expr) : MetaM Expr :=
  Meta.transform e (post := fun t => do
    if t.isApp && t.getAppArgs.back? == some v then
      if (← whnfD t) == y then return .done y
    return .continue)

partial def peel {α} (f : Flags) (e : Expr) (xs : Array Expr) (k : Array Expr → Expr → MetaM α) :
    MetaM α := do
  let e := e.consumeMData
  if let .forallE n t b bi := e then
    if f.classDec && bi.isInstImplicit then
      if let some v ← classicalInst? t then
        return ← peel f (b.instantiate1 v) xs k
    if f.subtype && !bi.isInstImplicit then
      if let some (α, p) ← subtype? t then
        return ← withLocalDecl n .default α fun y =>
          withLocalDecl (n.appendAfter "_prop") .default (p.beta #[y]) fun h => do
            let v ← mkAppOptM ``Subtype.mk #[α, p, y, h]
            peel f (← valToBase v y (b.instantiate1 v)) ((xs.push y).push h) k
    if f.exHyp && !b.hasLooseBVars then
      let t' := (← instantiateMVars t).consumeMData
      if t'.isAppOfArity ``Exists 2 then
        if let .lam xn xt xb _ := t'.appArg!.consumeMData then
          return ← withLocalDecl xn .default xt fun x =>
            peel f (.forallE n (xb.instantiate1 x) b bi) (xs.push x) k
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

/-- Drop data binders that nothing mentions and whose type is known to be nonempty. -/
def dropUnused (t : Tel) : MetaM Tel := do
  let n := t.fvars.size
  let mut keep := #[]
  for i in [:n] do
    let id := t.fvars[i]!.fvarId!
    let used := t.body.containsFVar id || (List.range n).any fun j => j > i && t.types[j]!.containsFVar id
    let drop ← if used || (← isProp t.types[i]!) then pure false else do
      let u ← getLevel t.types[i]!
      pure (← synthInstance? (mkApp (mkConst ``Nonempty [u]) t.types[i]!)).isSome
    unless drop do keep := keep.push i
  return { fvars := keep.map (t.fvars[·]!), types := keep.map (t.types[·]!), body := t.body }

/-- From position `i` on, replace each data binder that nothing mentions, and whose type is not
known to be nonempty, by a hypothesis `Nonempty T` in the same place. -/
partial def nonemptyHyps {α} (t : Tel) (i : Nat) (k : Tel → MetaM α) : MetaM α := do
  if h : i < t.fvars.size then
    let id := t.fvars[i].fvarId!
    let ty := t.types[i]!
    let n := t.fvars.size
    let used := t.body.containsFVar id || (List.range n).any fun j => j > i && t.types[j]!.containsFVar id
    if used || (← isProp ty) then return ← nonemptyHyps t (i + 1) k
    let ne := mkApp (mkConst ``Nonempty [← getLevel ty]) ty
    if (← synthInstance? ne).isSome then return ← nonemptyHyps t (i + 1) k
    let d ← id.getDecl
    withLocalDecl (d.userName.appendAfter "_nonempty") .default ne fun hne =>
      nonemptyHyps { t with fvars := t.fvars.set! i hne, types := t.types.set! i ne } (i + 1) k
  else k t

def withCanon {α} (f : Flags) (e : Expr) (k : Tel → MetaM α) : MetaM α :=
  peel f e #[] fun xs body => do
    let t : Tel := { fvars := xs, types := ← xs.mapM inferType, body }
    let t ← if f.bot then unpeelBot t else pure t
    let t ← if f.onePt then onePoint f.onePt2 t else pure t
    let t ← if f.dropUnused then dropUnused t else pure t
    if f.nonempty then nonemptyHyps t 0 k else k t

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

/-! ## Alignment by search (`align`) -/

/-- `>`, `≥`, `≠` in terms of `<`, `≤`, `¬ =`. -/
partial def nf (e : Expr) : Expr :=
  e.replace fun t =>
    match t with
    | .mdata _ b => some (nf b)
    | _ =>
      if t.isAppOfArity ``GT.gt 4 then
        some (mkApp4 (mkConst ``LT.lt t.getAppFn.constLevels!) (nf (t.getArg! 0)) (nf (t.getArg! 1))
          (nf (t.getArg! 3)) (nf (t.getArg! 2)))
      else if t.isAppOfArity ``GE.ge 4 then
        some (mkApp4 (mkConst ``LE.le t.getAppFn.constLevels!) (nf (t.getArg! 0)) (nf (t.getArg! 1))
          (nf (t.getArg! 3)) (nf (t.getArg! 2)))
      else if t.isAppOfArity ``Ne 3 then
        some (mkNot (mkApp3 (mkConst ``Eq t.getAppFn.constLevels!) (nf (t.getArg! 0)) (nf (t.getArg! 1))
          (nf (t.getArg! 2))))
      else none

def same (a b : Expr) : Bool :=
  a == b || match a.eq?, b.eq? with
    | some (t₁, x₁, y₁), some (t₂, x₂, y₂) => t₁ == t₂ && x₁ == y₂ && y₁ == x₂
    | _, _ => false

/-- Applications without loose bound variables, for the overlap score. -/
partial def subterms (e : Expr) (acc : Array Expr) : Array Expr :=
  let acc := if e.isApp && !e.hasLooseBVars then acc.push e else acc
  match e with
  | .app f a => subterms a (subterms f acc)
  | .forallE _ t b _ => subterms b (subterms t acc)
  | .lam _ t b _ => subterms b (subterms t acc)
  | .letE _ t v b _ => subterms b (subterms v (subterms t acc))
  | .mdata _ b => subterms b acc
  | .proj _ _ b => subterms b acc
  | _ => acc

/-- Hypotheses that coincide (as a multiset), and shared subterms mentioning an aligned binder. -/
def score (rt st : Tel) (rHyp sHyp : Array Bool) (src dst : Array Expr) : Nat × Nat := Id.run do
  let rH := (List.range rt.fvars.size).filter (rHyp[·]!) |>.toArray.map fun i => nf rt.types[i]!
  let sH := (List.range st.fvars.size).filter (sHyp[·]!) |>.toArray.map fun j =>
    nf (st.types[j]!.replaceFVars src dst)
  let rB := nf rt.body
  let sB := nf (st.body.replaceFVars src dst)
  let mut used := Array.replicate rH.size false
  let mut hits := if same rB sB then 1 else 0
  for h in sH do
    if let some i := (List.range rH.size).find? fun i => !used[i]! && same rH[i]! h then
      used := used.set! i true
      hits := hits + 1
  let ids := dst.map (·.fvarId!)
  let mentions (e : Expr) := (e.find? fun s => s.isFVar && ids.contains s.fvarId!).isSome
  let rSet : Std.HashSet Expr := ((rH.push rB).foldl (fun acc e => subterms e acc) #[]).foldl
    (fun s e => if mentions e then s.insert e else s) {}
  let sSet : Std.HashSet Expr := ((sH.push sB).foldl (fun acc e => subterms e acc) #[]).foldl
    (fun s e => if mentions e then s.insert e else s) {}
  return (hits, sSet.fold (fun n e => if rSet.contains e then n + 1 else n) 0)

/-- A complete or blocked assignment: data binders of `st` matched in order, the score, `src`, `dst`. -/
abbrev Leaf := Nat × (Nat × Nat) × Array Expr × Array Expr

def better (a b : Leaf) : Bool :=
  a.1 > b.1 || (a.1 == b.1 && (a.2.1.1 > b.2.1.1 || (a.2.1.1 == b.2.1.1 && a.2.1.2 > b.2.1.2)))

/-- Depth-first search over type-consistent assignments of the data binders `sIdx` of `st`, in
order, to unused data binders of `rt` before `cutR`, trying candidates in the order of `matchCut`
(same name first, then by position), so that the first leaf is the `CanonV2` choice. Keeps the
best leaf: most binders matched, then the best `score`, then the earliest. -/
partial def search (rt st : Tel) (rHyp sHyp : Array Bool) (cutR : Nat) (sIdx : Array Nat) (k : Nat)
    (used : Array Bool) (src dst : Array Expr) (best : IO.Ref (Option Leaf)) (leaves : IO.Ref Nat) :
    MetaM Unit := do
  if (← leaves.get) > permCap then return
  let finish : MetaM Unit := do
    leaves.modify (· + 1)
    let leaf : Leaf := (k, score rt st rHyp sHyp src dst, src, dst)
    match ← best.get with
    | some b => if better leaf b then best.set (some leaf)
    | none => best.set (some leaf)
  if h : k < sIdx.size then
    let j := sIdx[k]
    let x := st.fvars[j]!
    let dx ← x.fvarId!.getDecl
    let ty := st.types[j]!.replaceFVars src dst
    let mut named := #[]
    let mut other := #[]
    for i in [:cutR] do
      if rHyp[i]! || used[i]! then continue
      let di ← rt.fvars[i]!.fvarId!.getDecl
      if di.binderInfo.isInstImplicit != dx.binderInfo.isInstImplicit then continue
      if ← isDefEq ty rt.types[i]! then
        if di.userName == dx.userName then named := named.push i else other := other.push i
    if named.isEmpty && other.isEmpty then return ← finish
    for i in named ++ other do
      search rt st rHyp sHyp cutR sIdx (k + 1) (used.set! i true) (src.push x) (dst.push rt.fvars[i]!)
        best leaves
  else finish

/-- `matchCut` with the assignment at each step chosen by `search` instead of greedily; also returns
the number of leaves visited in the last step. -/
partial def matchCutPerm (rt st : Tel) (rHyp sHyp : Array Bool) (cutR cutS : Nat) :
    MetaM (Nat × Nat × Array Expr × Array Expr × Nat) := do
  let sIdx := (List.range cutS).filter (!sHyp[·]!) |>.toArray
  let best ← IO.mkRef none
  let leaves ← IO.mkRef 0
  search rt st rHyp sHyp cutR sIdx 0 (Array.replicate rt.fvars.size false) #[] #[] best leaves
  let some (k, _, src, dst) ← best.get | throwError "CANON_FAIL no assignment"
  let stopS := if h : k < sIdx.size then sIdx[k] else cutS
  let usedR := dst.filterMap (rt.fvars.idxOf? ·)
  let stopR := ((List.range cutR).find? fun i => !rHyp[i]! && !usedR.contains i).getD cutR
  if stopR == cutR && stopS == cutS then
    return (cutR, cutS, src, dst, ← leaves.get)
  matchCutPerm rt st rHyp sHyp stopR stopS

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

/-- Also returns the number of hypotheses after the cut that stay in the conclusion. -/
def split (f : Flags) (t : Tel) (hyp : Array Bool) (cut : Nat) :
    MetaM (Array Expr × Array Expr × Array Expr × Expr × Nat × Nat) := do
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
  return (xs, tys, hs, c, hoist.size, (keep.filter (hyp[·]!)).size)

/-- Role and type of the binder at which the aligned prefix stops, for diagnostics only. -/
def nextInfo (t : Tel) (hyp : Array Bool) (cut : Nat) : MetaM String := do
  if h : cut < t.fvars.size then
    let d ← t.fvars[cut].fvarId!.getDecl
    let role := if hyp[cut]! then "hyp" else if d.binderInfo.isInstImplicit then "inst" else "data"
    let used := t.body.containsFVar d.fvarId ||
      (t.types.extract (cut + 1) t.types.size).any (·.containsFVar d.fvarId)
    let ty := (toString (← ppExpr t.types[cut]!)).replace "\n" " " |>.replace "|" "/"
    return s!"[{role}|used={used}|{ty}]"
  return "[none]"

def goals (f : Flags) (R S : Expr) : MetaM (Array (Name × Expr) × String) := do
  let params (e : Expr) := (collectLevelParams {} e).params
  let mismatch := !((params R).all (params S).contains && (params S).all (params R).contains)
  let (R, S) := if f.univ0 || (f.univ0m && mismatch) then (univZero R, univZero S) else (R, S)
  let S ← if f.shuffle then shuffleRuns S else pure S
  let S := if f.anon then Id.run ((anonymize S).run' 0) else S
  withCanon f R fun rt => withCanon f S fun st => do
    let rHyp ← rt.types.mapM isProp
    let sHyp ← st.types.mapM isProp
    let greedy@(cutR, cutS, src, dst, ambiguous) ←
      matchCut rt st rHyp sHyp (depCut rt rHyp) (depCut st sHyp)
    let (cutR, cutS, src, dst, compared, moved) ← if f.perm then do
        let (cR, cS, sr, ds, n) ← matchCutPerm rt st rHyp sHyp (depCut rt rHyp) (depCut st sHyp)
        pure (cR, cS, sr, ds, n, cR != greedy.1 || cS != greedy.2.1 || ds != greedy.2.2.2.1)
      else pure (cutR, cutS, src, dst, 1, false)
    let (xs, tys, rh, rc, hoR, restR) ← split f rt rHyp cutR
    let (sxs, stys, sh, sc, hoS, restS) ← split f st sHyp cutS
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
    let map := dst.toList.map fun d => toString ((rt.fvars.idxOf? d).getD rt.fvars.size)
    let info := s!"ambiguous={ambiguous} full={full} prefix_r={cutR}/{rt.fvars.size} " ++
      s!"prefix_s={cutS}/{st.fvars.size} shared={xs.size} hoist_r={hoR} hoist_s={hoS}" ++
      s!" perm={compared} moved={moved} map={if map.isEmpty then "-" else ",".intercalate map}" ++
      s!" rest_hyp_r={restR} rest_hyp_s={restS}" ++
      s!" next_r={← nextInfo rt rHyp cutR} next_s={← nextInfo st sHyp cutS}"
    return (out, info)

def elabProp (stx : Term) : TermElabM Expr := do
  let e ← elabType stx
  synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  if e.hasMVar then throwError "CANON_FAIL metavariables in statement"
  return e

syntax (name := canon4Goals) "#canon4_goals " str str " (" term ")" " (" term ")" : command
syntax (name := canon4Prove) "canon4_prove " str ident " (" term ")" " (" term ")" ident " := " term : command

elab_rules : command
  | `(#canon4_goals $tag $fl ($r) ($s)) => liftTermElabM do
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
  | `(canon4_prove $fl $n:ident ($r) ($s) $g:ident := $pf) => liftTermElabM do
    let (gs, _) ← goals (Flags.parse fl.getString) (← elabProp r) (← elabProp s)
    let some (_, goal) := gs.find? (·.1 == g.getId) | throwError "unknown goal {g.getId}"
    let v ← elabTermEnsuringType pf goal
    synthesizeSyntheticMVarsNoPostponing
    let v ← instantiateMVars v
    if v.hasMVar then throwError "proof has metavariables"
    if v.hasSorry then logWarning "declaration uses 'sorry'"
    let lps := (collectLevelParams (collectLevelParams {} goal) v).params.toList
    addDecl <| .thmDecl { name := (← getCurrNamespace) ++ n.getId, levelParams := lps, type := goal, value := v }

end CanonV4
