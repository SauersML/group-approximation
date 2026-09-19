import GroupApproximation.Analysis.MFAlgebra
import GroupApproximation.Analysis.ReducedGroupCStarMFObstruction
import GroupApproximation.Analysis.ReducedGroupCStarSeparable
import GroupApproximation.Analysis.ReducedGroupCStarStablyFinite

/-!
# The reduced group C⋆-algebra of a non-MF group is separable, stably finite, not MF

This module formalizes the three printed sentences of `non_mf_groups_exist.tex`
that convert a non-MF group into a separable stably finite C⋆-algebra failing
the Blackadar–Kirchberg MF property.

* "For every countable group `G`, the reduced group algebra `C⋆_r(G)` is
  separable and has a faithful canonical trace, hence is stably finite."  The
  separability half is `ReducedGroupCStarTrace.reducedGroupCStar_separableSpace`
  of `Analysis.ReducedGroupCStarSeparable`; the stable-finiteness half is
  `reducedGroupCStar_isStablyFiniteCStarAlgebra` of
  `Analysis.ReducedGroupCStarStablyFinite`, which packages the canonical
  faithful trace of `Analysis.ReducedGroupCStarTraceFaithful`.  Both are proved
  there; nothing about traces is reproved here.
* "If `C⋆_r(G)` is MF, restricting an MF embedding to its canonical group
  unitaries shows that `G` is MF."  This is the composite of
  `HasMFEmbedding.isCDEOperatorMF` of `Analysis.MFAlgebra` with the faithful
  left regular unitary homomorphism `reducedLeftRegularUnitaryHom` of
  `Analysis.ReducedGroupCStarMFObstruction`.  The MF embedding supplied by
  `HasMFEmbedding` need not be unital, and the corner-complement correction
  `u ↦ e u + (1 - e 1)` that repairs this on unitaries is already carried out
  inside `MFAlgebra.nonUnitalStarAlgHomUnitaryMap`; it is used, not rebuilt.
* "Therefore a non-MF group automatically gives a separable stably finite
  reduced group C⋆-algebra that is not MF."  This is
  `reducedGroupCStar_separable_stablyFinite_not_isMFAlgebra`.

Note the direction carefully.  Everything below runs from an MF *algebra* to an
MF *group*, and contrapositively from a non-MF group to a non-unitally-embeddable
algebra.  The converse implication `IsCDEOperatorMF G → IsMFAlgebra
(ReducedGroupCStar G)` is **not** proved here, is not proved anywhere in this
repository, and is not claimed by the manuscript: an MF group gives a corona
representation of `G`, not of the norm closure of its complex group algebra
inside `B(ℓ²(G))`.  Accordingly no `↔` statement appears in this file.

`HasMFEmbedding` rather than `IsMFAlgebra` is the hypothesis of the implications,
so the obstruction does not covertly use separability; `IsMFAlgebra` enters only
in the packaged conclusions, where separability is available from
`Analysis.ReducedGroupCStarSeparable` anyway.
-/

namespace GroupApproximation

open ReducedGroupCStarTrace

universe u

/-- Restriction of an MF embedding to the canonical group unitaries.  If the
concrete reduced group C⋆-algebra of a countable group `G` admits a faithful,
possibly nonunital, star homomorphism into a norm-matrix corona, then `G`
itself has the literal Blackadar–Kirchberg CDE corona property.  The
representation used is the left regular one,
`reducedLeftRegularUnitaryHom`, which is faithful; the possible failure of the
embedding to be unital is absorbed by the corner-complement correction inside
`MFAlgebra.nonUnitalStarAlgHomUnitaryMap`. -/
theorem isCDEOperatorMF_of_hasMFEmbedding_reducedGroupCStar
    (G : Type u) [Group G] [Countable G]
    (h : HasMFEmbedding (ReducedGroupCStar G)) : IsCDEOperatorMF G :=
  h.isCDEOperatorMF (reducedLeftRegularUnitaryHom G)
    (reducedLeftRegularUnitaryHom_injective G)

/-- Contrapositive of the unitary restriction: a countable group that is not MF
has a concrete reduced group C⋆-algebra with no faithful star homomorphism into
any norm-matrix corona. -/
theorem not_hasMFEmbedding_reducedGroupCStar
    (G : Type u) [Group G] [Countable G] (h : ¬ IsCDEOperatorMF G) :
    ¬ HasMFEmbedding (ReducedGroupCStar G) :=
  mt (isCDEOperatorMF_of_hasMFEmbedding_reducedGroupCStar G) h

/-- The concrete reduced group C⋆-algebra of a countable non-MF group is not an
MF C⋆-algebra.  Only the embedding half of `IsMFAlgebra` is contradicted; the
separability half is in fact true, by
`ReducedGroupCStarTrace.reducedGroupCStar_separableSpace`. -/
theorem not_isMFAlgebra_reducedGroupCStar
    (G : Type u) [Group G] [Countable G] (h : ¬ IsCDEOperatorMF G) :
    ¬ IsMFAlgebra (ReducedGroupCStar G) :=
  fun hMF ↦ not_hasMFEmbedding_reducedGroupCStar G h hMF.2

/-- For every countable group, with no MF hypothesis whatsoever, the concrete
reduced group C⋆-algebra is separable and stably finite.  Separability comes
from countability of the generating left regular family; stable finiteness comes
from the canonical faithful trace. -/
theorem reducedGroupCStar_separable_stablyFinite
    (G : Type u) [Group G] [Countable G] :
    TopologicalSpace.SeparableSpace (ReducedGroupCStar G) ∧
      IsStablyFiniteCStarAlgebra (ReducedGroupCStar G) :=
  ⟨ReducedGroupCStarTrace.reducedGroupCStar_separableSpace G,
    reducedGroupCStar_isStablyFiniteCStarAlgebra G⟩

/-- The printed conclusion: a countable non-MF group automatically supplies a
separable, stably finite C⋆-algebra that is not MF, namely its own concrete
reduced group C⋆-algebra.  The first two conjuncts hold for every countable
group; only the third uses the failure of the MF property for `G`. -/
theorem reducedGroupCStar_separable_stablyFinite_not_isMFAlgebra
    (G : Type u) [Group G] [Countable G] (h : ¬ IsCDEOperatorMF G) :
    TopologicalSpace.SeparableSpace (ReducedGroupCStar G) ∧
      IsStablyFiniteCStarAlgebra (ReducedGroupCStar G) ∧
        ¬ IsMFAlgebra (ReducedGroupCStar G) :=
  ⟨(reducedGroupCStar_separable_stablyFinite G).1,
    (reducedGroupCStar_separable_stablyFinite G).2,
    not_isMFAlgebra_reducedGroupCStar G h⟩

end GroupApproximation

#print axioms GroupApproximation.isCDEOperatorMF_of_hasMFEmbedding_reducedGroupCStar
#print axioms GroupApproximation.not_hasMFEmbedding_reducedGroupCStar
#print axioms GroupApproximation.not_isMFAlgebra_reducedGroupCStar
#print axioms GroupApproximation.reducedGroupCStar_separable_stablyFinite
#print axioms GroupApproximation.reducedGroupCStar_separable_stablyFinite_not_isMFAlgebra
