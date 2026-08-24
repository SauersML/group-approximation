import GroupApproximation.Sofic.OpToHSShadowResidual
import GroupApproximation.Sofic.RadicalAutomorphization
import GroupApproximation.Sofic.SingleDefectSaturation
import GroupApproximation.Sofic.PushedDefectSaturation
import GroupApproximation.Sofic.DefectSaturation
import GroupApproximation.Sofic.SimpleFullMFRadical
import GroupApproximation.Sofic.NormMFResidualExactQuotient
import GroupApproximation.Sofic.NormMFUniversalCorona
import GroupApproximation.Sofic.FiveRadicalsCoincide
import GroupApproximation.Sofic.AlternatingLampVisibleQuotient
import GroupApproximation.Sofic.ManuscriptKazhdanTransport
import GroupApproximation.Algebra.VisibleQuotient
import GroupApproximation.Algebra.AlternatingLampNoncommensurable
import GroupApproximation.Computability.MFRadicalComputer

/-!
# Approximation radicals: the reading path

`Endpoint/Public` is the reading path for *what was proved*: a nonsofic group
exists, a finitely presented non-MF group exists.  This module is the reading
path for the reusable *mechanism* those results are instances of, which is a
different order and a different audience.

An approximation theory is a class of targets, and its radical is what every
homomorphism into that class kills.  The corpus turns out to contain a complete
four-step calculus for those radicals, and the declarations below are its
steps, each named against the module that proves it.  Nothing is proved here;
this module re-exports, so `#check` on any name lands on the real statement.

```text
   Produce  ──▶  Renormalize  ──▶  Saturate  ──▶  Separate
   one word      every scale       whole group    exact kernel
```

## Produce — a relation that approximation cannot see

The starting datum is one nontrivial element that some approximation-theoretic
shadow already kills.  The weakest useful such shadow is the operator-to-HS
residual `R_{∞→2}`: elements killed in the normalized-HS ultraproduct of every
operator-norm almost representation.

* `opToHSShadowResidual` — the shadow residual, as a subgroup.
* `opToHSShadowResidual_isFullyInvariant` and `map_opToHSShadowResidual_le` —
  it is fully invariant, hence normal and characteristic, and survives every
  homomorphism.  This functoriality is what lets a defect produced in a
  convenient source be carried into an inconvenient target.
* `normalClosure_le_opToHSShadowResidual` — one shadow word drags its whole
  normal closure in with it.
* `KazhdanAsymptoticCommutant.manuscriptCompressionRadical` — the analytic
  producer actually used: Kazhdan transport across a one-sided compression puts
  a compression-centralizer defect inside the norm-MF residual.
* `FournierFacioDefectData.exists_nontrivial_opToHSShadowBug` and
  `witness_commutator_mem_opToHSShadowResidual` — the produced datum in the
  form the compiler consumes: one nontrivial word in the shadow residual.
* `HasNontrivialOpToHSShadowBug` — that datum as a predicate on a group.

Note what this step does *not* claim.  Shadow membership is weaker than MF
radical membership; the inclusion `Rad_MF ≤ R_{∞→2}` is proved here
(`normMFResidual_eq_top_of_opToHSShadowResidual_eq_top` uses it in the
direction needed), while its strictness in general is a research-graph result
that has no Lean witness in this repository and is not asserted by any
declaration below.

## Renormalize — the same relation at every scale

`Sofic/RadicalAutomorphization` is the propagation step.  Given a *surjective*
endomorphism whose kernel is already invisible, the whole stable kernel
`K_∞(R) = ⋃_n ker(R^n)` is invisible too.

* `RadicalAutomorphization.stableKernel` and `mem_stableKernel_iff` — the
  stable kernel and its elementwise description.
* `RadicalAutomorphization.stableKernel_le_of_comap_le` — the engine, and the
  reason the step is cheap: its only hypothesis is `Rad.comap R ≤ Rad`, one
  inclusion of subgroups.  No surjectivity, no target class, no countability.
* `UniversalFactorization.coronaMFResidual_eq_comap` and its three companions
  `fdUnitaryResidual_eq_comap`, `finiteResidual_eq_comap`,
  `linearResidual_eq_comap` — what supplies that hypothesis, one per class of
  targets.
* `RadicalAutomorphization.stableKernel_le_coronaMFResidual`,
  `stableKernel_le_fdUnitaryResidual`, `stableKernel_le_finiteResidual`,
  `stableKernel_le_linearResidual` — the resulting propagation, for the MF
  radical, the finite-dimensional unitary residual, the finite residual, and
  the all-fields linear residual.
* `RadicalAutomorphization.exists_factorization_through_iterateEnd` — the
  representation-functor form: every corona representation factors through
  `R^n`, for every `n` at once.
* `RadicalAutomorphization.descendEquiv` and
  `stableKernel_le_of_injective_descent` — on `G ⧸ K_∞(R)` the descended map is
  an automorphism, and that quotient is the largest on which this happens.  The
  maximality statement is the engine lemma read backwards, with the radical
  replaced by an arbitrary subgroup.
* `RadicalAutomorphization.coronaMFResidual_eq_stableKernel` — the step closed:
  if the automorphization quotient is MF then the propagated kernel is the
  radical exactly.

## Saturate — until nothing is left visible

Routing the produced defect so that its normal closure fills the target turns a
local invisibility into total invisibility.

* `opToHSShadowResidual_eq_top_of_image_normalClosure_eq_top` — normal
  generation transports along the shadow residual.
* `normMFResidual_eq_top_of_opToHSShadowResidual_eq_top` — a group whose shadow
  residual is everything has full norm-MF residual.
* `normMFResidual_eq_top_of_shadow_bug_saturation` and
  `normMFResidual_eq_top_of_shadow_subgroup_saturation` — the two forms of the
  saturation endpoint, from one word and from a subgroup.
* `SingleDefectSaturation.SingleDefectRouterData.normMFResidual_eq_top`,
  `.isTwoGenerated`, `.quotient_not_isOperatorMF`,
  `.no_nontrivial_finite_quotient` — the routed output as an actual group: two
  generators, full MF residual, and no nontrivial homomorphism to a finite or
  operator-MF target, from that group *or any of its nontrivial quotients*.
* `PushedDefectSaturation.exists_nontrivial_twoGenerated_finitelyPresented_torsionFree_kazhdan_fullMFRadical_of_saturatingRouter`
  — the existence form, with the torsion-free and finite-presentation clauses.
* `DefectSaturation.actualCoronaMFResidual_eq_top_of_saturated` and
  `not_isCDEOperatorMF_of_saturated` — the same conclusion against the literal
  Carrión--Dadarlat--Eckhardt definition.
* `actualCoronaMFResidual_eq_top_of_isSimpleGroup` — the degenerate case that
  explains the mechanism: a simple group has no room for a partial radical, so
  one invisible element already forces the whole group.

The group-theoretic routing input itself — Higman embedding, Hull small
cancellation, and the acylindrical envelope — is not formalized here; the
declarations above are the analytic half, which takes the routing data as a
hypothesis and is unconditional given it.

## Separate — computing exactly what is forgotten

The last step turns the lower bound into an equality, and identifies the
quotient that every target in the class can see.

* `coronaMFResidual_eq_of_le_and_quotient_isOperatorMF` and
  `normMFResidual_eq_of_le_and_quotient_isOperatorMF` — the exact-radical
  criterion: a normal subgroup inside the radical whose quotient is MF *is* the
  radical.  This is what upgrades every obstruction theorem in the corpus from
  "something is invisible" to "exactly this is invisible".
* `existsUnique_quotient_factorization_to_normMatrixCorona` and
  `VisibleQuotient.existsUnique_factor` — the universal-quotient form: the
  whole representation functor is unchanged by passing to the quotient.
* `isOperatorMF_iff_normMFResidual_eq_bot` and `normMFQuotient_isOperatorMF` —
  the universal MF quotient is itself MF, and residual triviality characterizes
  operator MF for countable groups.
* `five_radicals_eq`, `five_radicals_eq_profinite`, and
  `bohrResidual_eq_finiteResidual` — the coincidence: for the compression
  wreath family one subgroup is simultaneously the MF radical, the
  finite-dimensional unitary residual, the all-fields linear residual, the Bohr
  radical and the finite residual, so all of those theories forget the *same*
  subgroup and share one universal visible quotient.
* `AlternatingLampLiteral.alternatingRadical_sandwich` and
  `actualCoronaMFResidual_eq_lampRange_iff` — the same computation for the
  alternating-lamp family, where the lamp group is perfect and the radical is
  the entire lamp.
* `not_mulEquiv_of_alternating_residual` and
  `not_mulEquiv_finiteIndex_of_alternating_residual` — what that buys: groups
  distinguished, up to commensurability, by data living entirely inside the
  subgroup all those theories erase.

## The consequence worth stating separately

Once "what MF forgets" is a computable object, it can be asked computational
questions, and the answers are not tame.

* `MFRadicalComputer.closed_package` — one fixed finitely presented group and a
  computable family of words, every one of them promised to lie in the MF
  radical, for which triviality is undecidable.
* `MFRadicalComputer.word_normMFInvisible`, `word_eq_one_iff_halts`, and
  `promised_word_problem_not_computable` — the three clauses separately.
* `MFRadicalComputer.word_mem_commutator_residual` — the hard words lie in
  `[Res_MF, U_MF]`, so the phenomenon is not a central or abelian artifact.

## Trust surface

Every name below is re-exported from a module in the root import closure, so
`scripts/Audit.lean` walks it like any other; nothing in this module adds a
hypothesis to anything it re-exports.
-/

namespace GroupApproximation.ApproximationRadicals

open GroupApproximation

/-! ### Produce -/

namespace Produce

export GroupApproximation
  (opToHSShadowResidual map_opToHSShadowResidual_le
    opToHSShadowResidual_isFullyInvariant
    normalClosure_le_opToHSShadowResidual
    normalKazhdan_le_normMFResidual_of_le_opToHSShadowResidual
    HasNontrivialOpToHSShadowBug)
export GroupApproximation.FournierFacioDefectData
  (witness_commutator_mem_opToHSShadowResidual
    exists_nontrivial_opToHSShadowBug)
export GroupApproximation.KazhdanAsymptoticCommutant
  (manuscriptCompressionRadical)

end Produce

/-! ### Renormalize -/

namespace Renormalize

export GroupApproximation.RadicalAutomorphization
  (stableKernel mem_stableKernel_iff ker_le_stableKernel
    stableKernel_le_of_comap_le stableKernel_le_of_injective_descent
    stableKernel_le_coronaMFResidual stableKernel_le_fdUnitaryResidual
    stableKernel_le_finiteResidual stableKernel_le_linearResidual
    exists_factorization_through_iterateEnd
    descend descendEquiv coronaMFResidual_eq_stableKernel)
export GroupApproximation.UniversalFactorization
  (coronaMFResidual_eq_comap fdUnitaryResidual_eq_comap
    finiteResidual_eq_comap linearResidual_eq_comap
    corona_comp_bijective exists_comp_eq)

end Renormalize

/-! ### Saturate -/

namespace Saturate

export GroupApproximation
  (normMFResidual_eq_top_of_opToHSShadowResidual_eq_top
    opToHSShadowResidual_eq_top_of_image_normalClosure_eq_top
    normMFResidual_eq_top_of_shadow_bug_saturation
    normMFResidual_eq_top_of_shadow_subgroup_saturation
    actualCoronaMFResidual_eq_top_of_isSimpleGroup
    actualCoronaMFInvisible_of_isSimpleGroup)
export GroupApproximation.SingleDefectSaturation.SingleDefectRouterData
  (normMFResidual_eq_top not_isOperatorMF quotient_not_isOperatorMF
    no_nontrivial_finite_quotient isTwoGenerated)
export GroupApproximation.PushedDefectSaturation
  (exists_nontrivial_twoGenerated_finitelyPresented_torsionFree_kazhdan_fullMFRadical_of_saturatingRouter)
export GroupApproximation.DefectSaturation
  (actualCoronaMFResidual_eq_top_of_saturated
    actualCoronaMFInvisible_of_saturated
    not_isCDEOperatorMF_of_saturated)

end Saturate

/-! ### Separate -/

namespace Separate

export GroupApproximation
  (coronaMFResidual_eq_of_le_and_quotient_isOperatorMF
    normMFResidual_eq_of_le_and_quotient_isOperatorMF
    normMFResidual_le_of_quotient_isOperatorMF
    existsUnique_quotient_factorization_to_normMatrixCorona
    isOperatorMF_iff_normMFResidual_eq_bot normMFQuotient_isOperatorMF
    five_radicals_eq five_radicals_eq_profinite bohrResidual_eq_finiteResidual
    not_mulEquiv_of_alternating_residual
    not_mulEquiv_finiteIndex_of_alternating_residual)
export GroupApproximation.VisibleQuotient (existsUnique_factor)
export GroupApproximation.AlternatingLampLiteral
  (alternatingRadical_sandwich actualCoronaMFResidual_eq_lampRange_iff)

end Separate

/-! ### The computational consequence -/

namespace Computer

export GroupApproximation.MFRadicalComputer
  (closed_package word_normMFInvisible word_eq_one_iff_halts
    word_mem_commutator_residual promised_word_problem_not_computable
    carrier_isFinitelyPresented carrier_not_isOperatorMF)

end Computer

end GroupApproximation.ApproximationRadicals
