import OAI.RingTheory.DirectFiniteness.Main
import OAI.Algebra.OddKaplansky.Main

/-! Independent check of two openai/math comparator challenges.

`Challenge.*` are verbatim copies of the statements in
`lean/ComparatorChallenges/{KaplanskyDirectFiniteness,OddKaplansky}.lean`
(only the namespace changed; `sourcePrime` refers to the solution's constant,
whose definition text is checked separately). The `rfl` theorems show the
solutions prove exactly those statements. -/

namespace Challenge

def KaplanskyClaim : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Fintype K) (_ : CharP K 2),
    ∃ (G : Type) (_ : Group G) (_ : Group.FG G),
      ∃ a b : MonoidAlgebra K G, a * b = 1 ∧ b * a ≠ 1

noncomputable section

def cellular {K G : Type} [Field K] [Group G]
    (d : MonoidAlgebra K G) (x : G → K) (g : G) : K :=
  d.coeff.sum fun u c => c * x (g * u)

open OAI.OddKaplansky in
def OddClaim : Prop :=
  sourcePrime.Prime ∧ Odd sourcePrime ∧
  ∃ (K : Type) (_ : Field K) (_ : Fintype K) (_ : CharP K sourcePrime),
    Fintype.card K = sourcePrime^4 ∧
    ∃ (G : Type) (_ : Group G) (_ : Group.FG G),
      (∃ g : G, g ≠ 1 ∧ IsOfFinOrder g) ∧
      ∃ a b : MonoidAlgebra K G,
        a * b = 1 ∧ b * a ≠ 1 ∧
        Function.Injective (cellular b) ∧ ¬ Function.Surjective (cellular b)

end

theorem kaplansky_same : KaplanskyClaim = OAI.KaplanskyCounterexample.MainClaim := rfl
theorem odd_same : OddClaim = OAI.OddKaplansky.MainClaim := rfl

end Challenge

#print axioms OAI.KaplanskyCounterexample.main_theorem
#print axioms OAI.OddKaplansky.main_theorem
#print axioms Challenge.kaplansky_same
#print axioms Challenge.odd_same
