import GroupApproximation.Analysis.GoldbringHartRoute
import GroupApproximation.Manuscript.OneSidedMFRadical.ReducedCStarConsequence

/-!
# `Relation to prior work`: the negative solution of the Connes embedding problem

`non_mf_groups_exist.tex`, subsection *"Relation to prior work"*:

> The negative solution of the Connes embedding problem [JNVWY] implies the
> existence of separable stably finite `C*`-algebras that are not MF
> [GH, Proposition 6.1 and Remark 6.2]; Theorem `thm:headline` gives one among
> reduced group `C*`-algebras.

`printedNegativeConnesEmbeddingSentence` below is that sentence, both clauses,
as one theorem.

## Which input is cited, and why

Exactly one: **the existence of the witness the Goldbring--Hart argument starts
from** — a separable, nontrivial, uniquely and faithfully traced unital
`C*`-algebra that does not embed into a tracial matrix ultraproduct.  That is
`NegativeConnesEmbeddingWitness`, and `negativeConnesEmbeddingWitness` is the
single `sorry` of this file.

Producing that witness is precisely the part of the printed sentence the
repository cannot reach: it is the negative solution of the Connes embedding
problem — a non-Connes-embeddable `II₁` factor, from `MIP* = RE` of Ji,
Natarajan, Vidick, Wright and Yuen — followed by the separable
elementary-substructure transfer of Goldbring--Hart's Remark 6.2, which
replaces that factor by a separable algebra with the same failure.  Neither a
predicate for Connes embeddability nor a von Neumann algebra is introduced
here; the witness is stated in the concrete matrix-ultraproduct vocabulary the
repository already has, which is exactly what the internal implication
consumes.

## What is proved rather than cited

Everything after the witness.  `separableStablyFiniteNonMF_of_negativeCEP` is an
unconditional implication, and its proof is the whole of Goldbring--Hart
Proposition 6.1 as formalized in `Analysis/GoldbringHartRoute.lean`:

* a faithful tracial state makes every finite matrix amplification finite, so
  the algebra is stably finite (`FaithfulTracialState.isStablyFiniteCStarAlgebra`);
* an MF embedding may be nonunital, and is corrected by passing to its support
  corner
  (`NonUnitalMFSupportCornerEmbedding.exists_injective_unital_supportCornerEmbedding`);
* an operator-norm-null sequence is Hilbert--Schmidt-null along any ultrafilter
  refining the cofinite filter, so the norm-matrix corona maps canonically to
  the tracial matrix quotient
  (`TracialUltraproduct.normMatrixCStarCoronaToTracialMatrixQuotient`); and
* uniqueness of the source trace makes that composite faithful
  (`TracialUltraproduct.injective_tracialMatrixQuotient_comp_of_unique_trace`),
  contradicting the choice of witness.

The three steps are packaged as
`stablyFinite_not_MF_of_not_isTraciallyMatrixEmbeddable`, which this file
applies once.

The second clause of the printed sentence needs no citation either:
`Manuscript/OneSidedMFRadical/ReducedCStarConsequence.lean` proves
`ReducedCStarConsequence` hypothesis-free, so the manuscript's own witness among
reduced group `C*`-algebras is already closed.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace PriorWork

/-- **The witness supplied by the negative solution of the Connes embedding
problem.**

There is a separable nontrivial unital `C*`-algebra with a unique faithful
tracial state which admits no faithful unital representation into a tracial
matrix ultraproduct over a free ultrafilter.

This is the hypothesis package of
`stablyFinite_not_MF_of_not_isTraciallyMatrixEmbeddable`, written as an
existential so that the algebra, its `C*`-structure, and its trace are all
bound inside the proposition.  It is stated in the repository's concrete
matrix-ultraproduct vocabulary: `IsTraciallyMatrixEmbeddable` mentions no
factor, no von Neumann algebra, and no literature hypothesis. -/
def NegativeConnesEmbeddingWitness : Prop :=
  ∃ (A : Type) (inst : CStarAlgebra A),
    letI : CStarAlgebra A := inst
    Nontrivial A ∧ TopologicalSpace.SeparableSpace A ∧
      ∃ tau : FaithfulTracialState A,
        (∀ sigma : TracialState A, ∀ a : A, sigma a = tau a) ∧
          ¬ IsTraciallyMatrixEmbeddable A

-- LITERATURE INPUT (sorry): Ji--Natarajan--Vidick--Wright--Yuen, MIP* = RE,
-- Commun. ACM 64 (2021), no. 11, 131--138, giving a non-Connes-embeddable II₁
-- factor; with Goldbring--Hart, Bull. Symbolic Logic 30 (2024), no. 2,
-- 181--198, Remark 6.2, for the separable elementary-substructure transfer.
/-- **The negative solution of the Connes embedding problem, in the form the
manuscript's sentence uses it.**

`MIP* = RE` refutes the Connes embedding problem, so some `II₁` factor `M` does
not embed into a tracial matrix ultrapower.  Regarded as a unital
`C*`-algebra, `M` is nontrivial and has a unique faithful trace, and
Goldbring--Hart's Remark 6.2 replaces it by a *separable* elementary
subalgebra with the same failure.  That separable algebra is the witness. -/
theorem negativeConnesEmbeddingWitness : NegativeConnesEmbeddingWitness :=
  sorry

/-- **The first clause of the printed sentence, as an unconditional
implication.**

> The negative solution of the Connes embedding problem implies the existence
> of separable stably finite `C*`-algebras that are not MF.

No literature input occurs in this proof: the witness is the hypothesis, and
the passage from it to the conclusion is the formalized Goldbring--Hart
argument `stablyFinite_not_MF_of_not_isTraciallyMatrixEmbeddable`. -/
theorem separableStablyFiniteNonMF_of_negativeCEP
    (h : NegativeConnesEmbeddingWitness) :
    OneSidedMFRadical.SeparableStablyFiniteNonMFCStarAlgebraExists := by
  obtain ⟨A, inst, hwitness⟩ := h
  letI : CStarAlgebra A := inst
  obtain ⟨hnt, hsep, tau, hunique, hnot⟩ := hwitness
  haveI : Nontrivial A := hnt
  haveI : TopologicalSpace.SeparableSpace A := hsep
  obtain ⟨hsf, hnotMF⟩ :=
    stablyFinite_not_MF_of_not_isTraciallyMatrixEmbeddable tau hunique hnot
  exact ⟨A, inst, hsep, hsf, hnotMF⟩

/-- **The printed sentence, both clauses.**

> The negative solution of the Connes embedding problem [JNVWY] implies the
> existence of separable stably finite `C*`-algebras that are not MF
> [GH, Proposition 6.1 and Remark 6.2]; Theorem `thm:headline` gives one among
> reduced group `C*`-algebras.

The first conjunct is the cited witness fed to the formalized implication; the
second is `manuscriptReducedCStarConsequence`, which is hypothesis-free and
says that `C*_r(H)` for the manuscript's group `H = EL₁₂(L_{𝔽₂}(1,2))` is
separable and stably finite but not MF.

The first conjunct is also provable with no citation at all, by
`manuscriptSeparableStablyFiniteNonMFCStarAlgebraExists`, which is the second
conjunct with the group forgotten.  What is recorded here is the printed
*attribution*: that the negative solution of the Connes embedding problem
already supplies such an algebra, independently of the manuscript's
construction. -/
theorem printedNegativeConnesEmbeddingSentence :
    OneSidedMFRadical.SeparableStablyFiniteNonMFCStarAlgebraExists ∧
      OneSidedMFRadical.ReducedCStarConsequence :=
  ⟨separableStablyFiniteNonMF_of_negativeCEP negativeConnesEmbeddingWitness,
    OneSidedMFRadical.manuscriptReducedCStarConsequence⟩

end PriorWork
end NonMF
end Manuscript
end GroupApproximation
