import ExperimentsMathlib.CanonV2

/-!
# Embedding alignment

When a data binder `y : T` of the reference `R` has no binder of the same type in the
candidate `S`, but some binder `x : T'` of `S` has a closed type that coerces into `T`,
the comparison is made along the coercion: `R'` is `R` with `y` replaced by `↑x`, and
`CanonV2.goals R' S` compares the two on the image. The extra goal `nsurj` says that the
first such coercion is not surjective, so `R` ranges over points that `S` never sees
(`prop:embed` / `off_image` in the theory draft).

`#embed_goals "tag" (R) (S)` prints `R'` and the goals; `embed_prove n (R) (S) g := proof`
checks `proof` against goal `g`.
-/

open Lean Meta Elab Command Term

namespace Embed

def coe? (x ty : Expr) : MetaM (Option Expr) := do
  match ← coerceSimple? x ty with
  | .some e => return some (← instantiateMVars e)
  | _ => return none

/-- Head symbol of a type; types headed by a variable share one key, since the two
telescopes bind different copies of the same type variables. -/
def headKey (ty : Expr) : Name :=
  match ty.consumeMData.getAppFn with
  | .const n _ => n
  | .fvar _ => `_var
  | _ => `_other

/-- For each binder of `rt`, the `(name, type)` of the candidate binder it is embedded from.
Only non-function types are embedded, and only when no candidate binder has a type with
the same head symbol. -/
def plan (rt st : CanonV2.Tel) : MetaM (Array (Option (Name × Expr))) := do
  let mut used : Array Nat := #[]
  let mut out := #[]
  for i in [:rt.fvars.size] do
    let x := rt.fvars[i]!
    let ty := rt.types[i]!
    unless (← CanonV2.isData x ty) && !(← whnfR ty).isForall && headKey ty != `_other do
      out := out.push none
      continue
    let same ← (List.range st.fvars.size).anyM fun j => do
      return (← CanonV2.isData st.fvars[j]! st.types[j]!) && headKey st.types[j]! == headKey ty
    if same then
      out := out.push none
      continue
    let rn := (← x.fvarId!.getDecl).userName
    let mut cands := #[]
    for j in [:st.fvars.size] do
      if used.contains j then continue
      let sty := st.types[j]!
      unless ← CanonV2.isData st.fvars[j]! sty do continue
      if sty.hasFVar then continue
      let sn := (← st.fvars[j]!.fvarId!.getDecl).userName
      let ok ← withLocalDecl sn .default sty fun z => return (← coe? z ty).isSome
      if ok then cands := cands.push (j, sn, sty)
    let pick := (cands.find? (·.2.1 == rn)) <|> cands[0]?
    match pick with
    | some (j, sn, sty) =>
      used := used.push j
      out := out.push (some (sn, sty))
    | none => out := out.push none
  return out

partial def build (rt : CanonV2.Tel) (pl : Array (Option (Name × Expr))) (i : Nat)
    (xs tys src dst : Array Expr) : MetaM Expr := do
  if i == rt.fvars.size then
    return ← CanonV2.close xs tys (rt.body.replaceFVars src dst)
  let ty := rt.types[i]!.replaceFVars src dst
  match pl[i]! with
  | none => build rt pl (i + 1) (xs.push rt.fvars[i]!) (tys.push ty) src dst
  | some (n, sty) =>
    withLocalDecl n .default sty fun z => do
      let some e ← coe? z ty | throwError "coercion failed"
      build rt pl (i + 1) (xs.push z) (tys.push sty) (src.push rt.fvars[i]!) (dst.push e)

/-- `R'` and the non-surjectivity goal of the first embedded binder. -/
def embed (R S : Expr) : MetaM (Expr × Expr) :=
  CanonV2.withCanon R fun rt => CanonV2.withCanon S fun st => do
    let pl ← plan rt st
    let some i := pl.findIdx? Option.isSome | throwError "no embedding"
    let some (n, sty) := pl[i]! | unreachable!
    let R' ← build rt pl 0 #[] #[] #[] #[]
    let ty := rt.types[i]!
    let surj ← withLocalDecl `y .default ty fun y => withLocalDecl n .default sty fun z => do
      let some e ← coe? z ty | throwError "coercion failed"
      mkForallFVars #[y] (← mkAppM ``Exists #[← mkLambdaFVars #[z] (← mkEq e y)])
    let pre := rt.fvars.extract 0 i
    return (R', mkNot (← CanonV2.close pre (rt.types.extract 0 i) surj))

def goals (R S : Expr) : MetaM (Expr × Array (Name × Expr) × String) := do
  let (R', nsurj) ← embed R S
  let (gs, info) ← CanonV2.goals R' S
  return (R', gs.push (`nsurj, nsurj), info)

syntax (name := embedGoals) "#embed_goals " str " (" term ")" " (" term ")" : command
syntax (name := embedProve) "embed_prove " ident " (" term ")" " (" term ")" ident " := " term : command

elab_rules : command
  | `(#embed_goals $tag ($r) ($s)) => liftTermElabM do
    let tag := tag.getString
    try
      let (R', gs, info) ← goals (← CanonV2.elabProp r) (← CanonV2.elabProp s)
      let mut msg := m!"CANON_BEGIN {tag}\nCANON_INFO {info}\nCANON_EMBED {R'}"
      for (n, g) in gs do
        msg := msg ++ m!"\nCANON_GOAL {n} ::: {g}"
      logInfo (msg ++ m!"\nCANON_END {tag}")
    catch e =>
      logInfo m!"CANON_BEGIN {tag}\nCANON_FAIL {e.toMessageData}\nCANON_END {tag}"

elab_rules : command
  | `(embed_prove $n:ident ($r) ($s) $g:ident := $pf) => liftTermElabM do
    let (_, gs, _) ← goals (← CanonV2.elabProp r) (← CanonV2.elabProp s)
    let some (_, goal) := gs.find? (·.1 == g.getId) | throwError "unknown goal {g.getId}"
    let v ← elabTermEnsuringType pf goal
    synthesizeSyntheticMVarsNoPostponing
    let v ← instantiateMVars v
    if v.hasMVar then throwError "proof has metavariables"
    if v.hasSorry then logWarning "declaration uses 'sorry'"
    let lps := (collectLevelParams (collectLevelParams {} goal) v).params.toList
    addDecl <| .thmDecl { name := (← getCurrNamespace) ++ n.getId, levelParams := lps, type := goal, value := v }

end Embed
