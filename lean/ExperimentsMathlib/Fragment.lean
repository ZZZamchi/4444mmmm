import ExperimentsMathlib.CanonV2

/-!
# Syntactic fragment of a statement

`#fragment "tag" (R)` canonicalizes `R` and prints

* `FRAG_DATA`: head constants of the types of the data binders (`Nat`, `Real`, `Set`, `pi`, ...);
* `FRAG_INST`: head constants of the instance-implicit binders (`Group`, `Field`, ...);
* `FRAG_CONSTS`: every constant occurring in the hypotheses and the conclusion;
* `FRAG_FLAGS`: `mul_nonlit` (a product of two non-literals), `pow_nonlit` (a power with a
  non-literal exponent), `div_nonlit`, `mod_nonlit`, `dvd_nonlit` (division, remainder or
  divisibility by a non-literal), `binder_quant` (a quantifier inside a component).

The classification into Presburger / real-closed / general arithmetic / other is done by the
caller from these facts.
-/

open Lean Meta Elab Command Term

namespace Fragment

def headName (ty : Expr) : Name :=
  match ty with
  | .forallE .. => `pi
  | .sort .. => `sort
  | _ => match ty.getAppFn with
    | .const n _ => n
    | _ => `other

def isLit (e : Expr) : Bool :=
  e.isRawNatLit || e.isAppOfArity ``OfNat.ofNat 3 ||
    (e.isAppOfArity ``Neg.neg 3 && (e.getArg! 2).isRawNatLit) ||
    (e.isAppOfArity ``Neg.neg 3 && (e.getArg! 2).isAppOfArity ``OfNat.ofNat 3) ||
    (e.isAppOfArity ``Nat.cast 3 && (e.getArg! 2).isAppOfArity ``OfNat.ofNat 3) ||
    (e.isAppOfArity ``Int.cast 3 && (e.getArg! 2).isAppOfArity ``OfNat.ofNat 3)

partial def flags (e : Expr) (acc : Std.HashSet String) : Std.HashSet String :=
  let acc :=
    if e.isAppOfArity ``HMul.hMul 6 && !isLit (e.getArg! 4) && !isLit (e.getArg! 5) then
      acc.insert "mul_nonlit"
    else if e.isAppOfArity ``HPow.hPow 6 && !isLit (e.getArg! 5) then acc.insert "pow_nonlit"
    else if e.isAppOfArity ``HDiv.hDiv 6 && !isLit (e.getArg! 5) then acc.insert "div_nonlit"
    else if e.isAppOfArity ``HMod.hMod 6 && !isLit (e.getArg! 5) then acc.insert "mod_nonlit"
    else if e.isAppOfArity ``Dvd.dvd 4 && !isLit (e.getArg! 2) then acc.insert "dvd_nonlit"
    else acc
  match e with
  | .app f a => flags a (flags f acc)
  | .lam _ t b _ => flags b (flags t (acc.insert "binder_quant"))
  | .forallE _ t b _ => flags b (flags t (acc.insert "binder_quant"))
  | .letE _ t v b _ => flags b (flags v (flags t acc))
  | .mdata _ b => flags b acc
  | .proj _ _ b => flags b acc
  | _ => acc

def report (tag : String) (R : Expr) : MetaM MessageData :=
  CanonV2.withCanon R fun t => do
    let mut data : Array Name := #[]
    let mut inst : Array Name := #[]
    let mut comps : Array Expr := #[t.body]
    for i in [:t.fvars.size] do
      let x := t.fvars[i]!
      let ty := t.types[i]!
      let d ← x.fvarId!.getDecl
      if d.binderInfo.isInstImplicit then inst := inst.push (headName ty)
      else if ← isProp ty then comps := comps.push ty
      else data := data.push (headName ty)
    let mut consts : Std.HashSet Name := {}
    let mut fl : Std.HashSet String := {}
    for c in comps do
      consts := c.foldConsts consts fun n s => s.insert n
      fl := flags c fl
    let sortNames (xs : Array Name) : List String :=
      (xs.toList.map toString).mergeSort (· ≤ ·)
    return m!"FRAG_BEGIN {tag}\nFRAG_DATA {" ".intercalate (sortNames data)}\n" ++
      m!"FRAG_INST {" ".intercalate (sortNames inst)}\n" ++
      m!"FRAG_CONSTS {" ".intercalate (sortNames consts.toArray)}\n" ++
      m!"FRAG_FLAGS {" ".intercalate (fl.toList.mergeSort (· ≤ ·))}\nFRAG_END {tag}"

syntax (name := fragmentCmd) "#fragment " str " (" term ")" : command

elab_rules : command
  | `(#fragment $tag ($r)) => liftTermElabM do
    let tag := tag.getString
    try
      logInfo (← report tag (← CanonV2.elabProp r))
    catch e =>
      logInfo m!"FRAG_BEGIN {tag}\nFRAG_FAIL {e.toMessageData}\nFRAG_END {tag}"

end Fragment

section test

-- Only core types here; `CanonV2` does not import Mathlib. Experiments import Mathlib first.
#fragment "t1" (∀ n : Nat, 0 < n → n + 1 ≤ 2 * n)
#fragment "t2" (∀ x y : Int, 0 < x → x * y ≤ x ^ 2 + y ^ 2)
#fragment "t3" (∀ (α : Type) [Inhabited α] (a b : α), a = b → ∀ n : Nat, n % 2 = 0 → a = b)
#fragment "t4" (∀ f : Nat → Nat, (∀ n, f n ∣ f (n + 1)) → ∀ n, f 0 ∣ f n)

end test
