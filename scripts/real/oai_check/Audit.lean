import OAI.RingTheory.DirectFiniteness.FinitelyPresented
import OAI.Algebra.OddKaplansky.Main

/-! Three-valued audit of the two Kaplansky challenges against the manuscripts.

Characteristic two. `Paper` is Theorem 1.1 of the manuscript (OpenAI's own challenge
`KaplanskyFinitelyPresented`); `Challenge` is the main challenge `KaplanskyDirectFiniteness`.
Both are kernel-checked, so they are closed-equivalent (`closed_equiv`). Over the shared
existential prefix `(K, G)` they have the same conclusion and different hypotheses on `G`,
and the trivial group separates the hypotheses (`hyp_differ`): component verdict reject.

Odd characteristic. The title reads either as `TitleExists` (some odd prime) or as
`TitleForall` (every odd prime). The challenge proves `TitleExists`. Against
`TitleForall` it is the restriction along `() ↦ sourcePrime` (`forall_restrict`), and
there are odd primes off that image (`off_image`); the challenge says nothing there. -/

namespace Audit

def DF (K G : Type) [Field K] [Group G] : Prop :=
  ∃ a b : MonoidAlgebra K G, a * b = 1 ∧ b * a ≠ 1

def OddTorsion (G : Type) [Group G] : Prop :=
  ∃ (ℓ : ℕ) (_ : ℓ.Prime) (_ : Odd ℓ) (g : G), orderOf g = ℓ

def Paper : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Fintype K) (_ : CharP K 2),
    ∃ (G : Type) (_ : Group G) (_ : Group.IsFinitelyPresented G), OddTorsion G ∧ DF K G

def Challenge : Prop := OAI.KaplanskyCounterexample.MainClaim

theorem paper_holds : Paper := OAI.KaplanskyCounterexample.finitelyPresented_counterexample

theorem challenge_holds : Challenge := OAI.KaplanskyCounterexample.main_theorem

theorem closed_equiv : Paper ↔ Challenge := ⟨fun _ => challenge_holds, fun _ => paper_holds⟩

theorem not_oddTorsion_unit : ¬ OddTorsion Unit := by
  rintro ⟨ℓ, hp, -, g, hg⟩
  rw [orderOf_eq_one_iff.mpr (Subsingleton.elim g 1)] at hg
  exact Nat.not_prime_one (hg ▸ hp)

theorem hyp_differ : Group.FG Unit ∧ ¬ (Group.IsFinitelyPresented Unit ∧ OddTorsion Unit) :=
  ⟨inferInstance, fun h => not_oddTorsion_unit h.2⟩

/-- Pointwise comparison of the hypotheses over the shared prefix fails. -/
theorem not_hyp_equiv :
    ¬ ∀ (K : Type) [Field K] [Fintype K] [CharP K 2] (G : Type) [Group G],
      (Group.IsFinitelyPresented G ∧ OddTorsion G) ↔ Group.FG G :=
  fun h => hyp_differ.2 ((h (ZMod 2) Unit).2 hyp_differ.1)

open OAI.OddKaplansky

def OddDF (p : ℕ) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Fintype K) (_ : CharP K p),
    ∃ (G : Type) (_ : Group G) (_ : Group.FG G), DF K G

def TitleExists : Prop := ∃ p, p.Prime ∧ Odd p ∧ OddDF p

def TitleForall : Prop := ∀ p, p.Prime → Odd p → OddDF p

theorem main_gives_point (h : MainClaim) : OddDF sourcePrime := by
  obtain ⟨-, -, K, iF, iFt, iC, -, G, iG, iFG, -, a, b, hab, hba, -⟩ := h
  exact ⟨K, iF, iFt, iC, G, iG, iFG, a, b, hab, hba⟩

theorem title_exists : TitleExists :=
  ⟨sourcePrime, main_theorem.1, main_theorem.2.1, main_gives_point main_theorem⟩

theorem forall_restrict (h : TitleForall) : OddDF sourcePrime :=
  h _ main_theorem.1 main_theorem.2.1

theorem off_image : ∃ p, p.Prime ∧ Odd p ∧ p ≠ sourcePrime := by
  by_cases h : sourcePrime = 3
  · exact ⟨5, by norm_num, by decide, by rw [h]; decide⟩
  · exact ⟨3, by norm_num, by decide, Ne.symm h⟩

end Audit

#print axioms Audit.closed_equiv
#print axioms Audit.not_hyp_equiv
#print axioms Audit.title_exists
#print axioms Audit.off_image
