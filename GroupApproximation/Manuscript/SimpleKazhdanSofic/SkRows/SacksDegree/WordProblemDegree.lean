import GroupApproximation.Manuscript.SimpleKazhdanSofic.SkRows.SacksDegree.Antichain
import GroupApproximation.Manuscript.SimpleKazhdanSofic.WordProblemsCorollaryAssembly
import GroupApproximation.Manuscript.SimpleKazhdanSofic.SturmianComputability
import GroupApproximation.Meta.AxiomGuard

/-!
# The Turing degree of the word problem of `G_{X_α}`

`simple_kazhdan_sofic_group.tex`, proof of `cor:wp`, tex l.719–721:

> By a construction of Sacks, the Turing degrees contain an antichain of size
> continuum~\cite[Chapter~V]{Odifreddi}, and the groups $G_{X_\alpha}$ with $\alpha$ of these
> degrees are as claimed.

The degree of the word problem of a finitely generated group does not depend on the finite
generating family. This module records that as an equality in Mathlib's `TuringDegree`, and defines
the map `α ↦ deg WP(G_{X_α})` used in `SturmianAntichain.lean`.

* `wordProblemDegree s`: the degree of the word problem oracle of the family `s`;
* `wordProblemDegree_eq_of_generating`: two finite generating families of one group give the same
  degree (`turingReducible_wordProblemOracle_of_generates`, closed, in both directions);
* `sturmianWordProblemDegree α`: the degree of the word problem of `G_{X_α}` for its standard
  generators `genValue`;
* `sturmianWordProblemDegree_eq`: it is the word problem degree of every finite generating family of
  `G_{X_α}` (`closure_range_genValue`, closed).
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic
namespace SkRows
namespace SacksDegree

open Set

/-- The Turing degree of the word problem of a group for the generating family `s`. -/
noncomputable def wordProblemDegree {ι H : Type} [Group H] [Primcodable ι] (s : ι → H) :
    TuringDegree :=
  turingDegreeOf (wordProblemOracle s)

/-- The word problem degree does not depend on the finite generating family. -/
theorem wordProblemDegree_eq_of_generating {H ι κ : Type} [Group H] [Primcodable ι]
    [Primcodable κ] [Finite ι] [Finite κ] (s : ι → H) (t : κ → H)
    (hs : Subgroup.closure (range s) = ⊤) (ht : Subgroup.closure (range t) = ⊤) :
    wordProblemDegree s = wordProblemDegree t :=
  (turingDegreeOf_eq_iff _ _).2
    ⟨turingReducible_wordProblemOracle_of_generates ht s,
      turingReducible_wordProblemOracle_of_generates hs t⟩

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SacksDegree.wordProblemDegree_eq_of_generating

/-- `α ↦ deg WP(G_{X_α})`: the Turing degree of the word problem of the group `G_{X_α}` of the
Sturmian subshift of slope `α`, for its standard generators. -/
noncomputable def sturmianWordProblemDegree (α : ℝ) : TuringDegree :=
  wordProblemDegree (genValue (sturmianSubshift α))

/-- `sturmianWordProblemDegree α` is the word problem degree of every finite generating family of
`G_{X_α}`. -/
theorem sturmianWordProblemDegree_eq (α : ℝ) {κ : Type} [Primcodable κ] [Finite κ]
    (t : κ → G (sturmianSubshift α)) (ht : Subgroup.closure (range t) = ⊤) :
    sturmianWordProblemDegree α = wordProblemDegree t := by
  haveI : Finite (Coeff Bool) := Finite.of_equiv _ (Coeff.equivOption Bool).symm
  exact wordProblemDegree_eq_of_generating _ t (closure_range_genValue _) ht

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SacksDegree.sturmianWordProblemDegree_eq

end SacksDegree
end SkRows
end SimpleKazhdanSofic
end GroupApproximation
