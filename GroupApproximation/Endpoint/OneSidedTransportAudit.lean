import GroupApproximation.Meta.AxiomGuard
import GroupApproximation.Manuscript.OneSidedMFRadical.LiteralMFClosure
import GroupApproximation.Manuscript.OneSidedMFRadical.ResidualCalculus
import GroupApproximation.Manuscript.OneSidedMFRadical.FiniteDimensionalCommutant
import GroupApproximation.Manuscript.OneSidedMFRadical.StableFiniteness
import GroupApproximation.Manuscript.OneSidedMFRadical.UniversalFactorization
import GroupApproximation.Manuscript.OneSidedMFRadical.PrescribedQuotients
import GroupApproximation.Manuscript.OneSidedMFRadical.DefectHS
import GroupApproximation.Manuscript.OneSidedMFRadical.KazhdanTransport
import GroupApproximation.Manuscript.OneSidedMFRadical.NormalKazhdan
import GroupApproximation.Manuscript.OneSidedMFRadical.KazhdanProjectionOrder
import GroupApproximation.Manuscript.OneSidedMFRadical.CentralCoronaCorner
import GroupApproximation.Manuscript.OneSidedMFRadical.CompressionCriterion
import GroupApproximation.Manuscript.OneSidedMFRadical.DefectSaturation
import GroupApproximation.Manuscript.OneSidedMFRadical.ShadowResidual
import GroupApproximation.Manuscript.OneSidedMFRadical.PrintedDefectShadow
import GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveConfiguration
import GroupApproximation.Leavitt.LeavittMarkNontrivial
import GroupApproximation.Leavitt.LeavittMatrixCompression

/-!
# Kernel audit for *One-sided Kazhdan transport and MF radicals*

Every numbered statement and every displayed equation of
`non_mf_groups_exist.tex` is printed here, and
`metadata/ONESIDED_TRANSPORT_LEDGER.md` has one row for each.
`scripts/check_onesided_transport_ledger.py` keeps the two in step in both
directions: a row may not name a declaration this file does not print, and
this file may not print a closed endpoint the ledger does not list.

`#audit_closed_axioms` does two things.  It fails the build if the axiom
closure of the proof contains anything beyond `propext`, `Classical.choice`
and `Quot.sound`, and it rejects any declaration whose type begins with a
caller-supplied binder.  The second half is what matters for an existence
headline: it is the machine check that a theorem is not quietly carrying
`(hSimple : IsSimpleGroup H)` or `(hConfiguration : ...)` as an
innocuous-looking manuscript parameter.  The manuscript's own quantifiers
therefore live inside named propositions -- `OneSidedCompressionCriterion`,
`PrescribedMFQuotients`, `PropositionDefect`, ... -- where the binder check is
supposed to find them, and not in front.

Three groups of declarations are printed with the weaker `#audit_axioms`,
which reports the closure without the binder check:

* the **one genuinely conditional endpoint**, `headlineConclusion_of`.  Its
  leading hypothesis is `PropositionSimple`, that is `IsSimpleGroup H`, which
  the repository does not prove; the manuscript obtains it from Preusser's
  normal-subgroup theorem.  A green build here says its *proof* contains no
  hidden postulate.  It does not erase the displayed hypothesis, and no closed
  endpoint above or below depends on it -- in particular
  `rankTwelve_actualCoronaMFResidual_eq_top`, the displayed conclusion
  `Rad_MF(H) = H` of Theorem B, is closed and is proved through normal
  generation of the single element `d = e02(q)`, not through simplicity.
* the **printed definitions and the lemmas over arbitrary data** -- the
  compression-centralizer defect, the compression `Psi`, the corner
  conjugation, the amalgam.  These take the manuscript's own data (a group, a
  Leavitt family, a homomorphism) as leading binders, so they cannot have an
  empty telescope; they assume nothing, and each is consumed by a closed
  endpoint above.
* the **implementation lemmas** the closed endpoints are assembled from,
  audited at their own statements so that the manuscript rows are not the only
  place their closure is checked.
-/

/-! ## Section 1: the MF radical, the defect, and the three theorems -/

#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptMFResidualCalculusLiteral
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptMFResidualCalculus
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptLiteralMFClosureIsQuotientPullback
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptMFRadicalIsLiteralClosureOfTrivial
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptFullRadicalKillsMFTargets

-- Theorem A, printed as one theorem with four clauses, and its two exact
-- constituents.
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptCompleteOneSidedCompressionCriterion
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptOneSidedCompressionCriterion
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrintedDefectFiniteDimensionalSterility

-- The sterility paragraph.  The amenable case is not claimed: only the
-- group-theoretic half, `L` finite, is proved.  See the ledger.
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrintedDefectSterility

-- Theorem B.  The displayed conclusion and the structural clauses are closed;
-- the printed adjective "simple" is not, and is audited below.
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveEndpoint.leavittFamily
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveEndpoint.rankTwelve_actualCoronaMFResidual_eq_top
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveEndpoint.closedStructuralProfile

-- `eq:basic-defect`: the introduction's display of Corollary `cor:defect-hs`.
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptCompressionDefectHSInvisible

-- Theorem C.
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrescribedMFQuotients

/-! ## Section 2: one-sided compression in finite dimension -/

#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptFiniteDimensionalCommutantRigidity

/-! ## Section 3: Kazhdan transport in normalized Hilbert--Schmidt norm -/

#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptShadowResidualIsIntersectionOfHSKernels
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptShadowResidualIsNormal
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptNormMatrixCoronaStableFinite
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptOneSidedKazhdanProjectionOrder
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptOneSidedKazhdanTransport

/-! ## Section 4: the canonical Kazhdan sector and the MF radical -/

#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptCentralCoronaCorner
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptNormalKazhdanRadical
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrintedDefectShadowInclusion
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrintedDefectNormalKazhdanRadical
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptDefectSaturation

/-! ## Section 5: the binary Leavitt self-compression -/

#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveEndpoint.q_ne_zero
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveEndpoint.printedTauGL
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveEndpoint.tauUnit_eq_six_elementary
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveEndpoint.printedTauGL_mem
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveEndpoint.corner_hasKazhdanPropertyT
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveEndpoint.printedDefectConfiguration

/-! ## Section 6: the full MF radical -/

#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveEndpoint.manuscriptPropositionDefect
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveEndpoint.tau_conj_c

/-! ## Section 7: prescribed MF quotients -/

#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptSplitPrescribedProjection
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptUniversalFactorization
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrescribedQuotientRelationCalculus

/-! ## The one conditional endpoint

`prop:simple` has no proof in this repository, so Theorem B is available only
as an implication.  The hypothesis is deliberately left in front, where the
binder check can see it, rather than folded into a named proposition where it
could not.  The second hypothesis of this implication is discharged in-repo by
`rankTwelve_actualCoronaMFResidual_eq_top`, which is closed above; the first
is not discharged anywhere. -/

#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveEndpoint.headlineConclusion_of

/-! ## Printed definitions and statements over arbitrary manuscript data

These carry no assumption.  Their types begin with the group, the ring, the
Leavitt family or the homomorphism that the manuscript itself quantifies over,
which is why the closed macro cannot accept them. -/

#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.printedDefect
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.map_printedDefect_to_range_le
#audit_axioms GroupApproximation.LeavittFamily.matrixCompression
#audit_axioms GroupApproximation.RankTwelve.tau_fullCorner_tauInv
#audit_axioms GroupApproximation.MFCamouflage.Camouflage

/-! ## Implementation lemmas

Audited at their own statements, so that the manuscript rows above are not the
only place their axiom closure is checked. -/

-- The printed defect: its generating set, its generators, and the containment
-- in the development's larger compressor-group defect.
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.printedDefectSet
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.printedDefect_generator_mem
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.printedDefect_le_compressionCentralizerDefect

-- The ordinary-limit `K_2(V)` and the printed MF closure.
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.hsKernel
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.literalMFClosure

-- `eq:pq`: the two Leavitt relations behind `q ≠ 0`.
#audit_axioms GroupApproximation.LeavittFamily.p0_add_p1
#audit_axioms GroupApproximation.LeavittFamily.t1_mul_p1_mul_s1

-- `eq:matrix-compression`: unitality, multiplicativity, the recovery identity
-- that gives injectivity, and the elementary-matrix formula.
#audit_axioms GroupApproximation.LeavittFamily.matrixCompression_one
#audit_axioms GroupApproximation.LeavittFamily.matrixCompression_mul
#audit_axioms GroupApproximation.LeavittFamily.matrixCompression_recover
#audit_axioms GroupApproximation.LeavittFamily.matrixCompressionHom_injective
#audit_axioms GroupApproximation.LeavittFamily.matrixCompression_elementaryUnit

-- `X`, `Y`, `XY = YX = I`, the nested `tau`, the Whitehead factorization and
-- the corner conjugation, over an arbitrary Leavitt family.
#audit_axioms GroupApproximation.RankTwelve.shift
#audit_axioms GroupApproximation.RankTwelve.shiftInv
#audit_axioms GroupApproximation.RankTwelve.shift_mul_shiftInv
#audit_axioms GroupApproximation.RankTwelve.shiftInv_mul_shift
#audit_axioms GroupApproximation.RankTwelve.tau
#audit_axioms GroupApproximation.RankTwelve.tau_eq_whitehead_product
#audit_axioms GroupApproximation.RankTwelve.shift_halfCorner_shiftInv

-- The concrete rank-twelve configuration behind `prop:defect`.
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveEndpoint.tau_conj_corner_elementaryRoot
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveEndpoint.tau_compresses_corner
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveEndpoint.c_commutes_corner
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveEndpoint.tau_c_commutator_ell
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveEndpoint.defect_ne_one
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveEndpoint.normalClosure_defect_eq_top

-- The amalgam of Section 7.
#audit_axioms GroupApproximation.MFCamouflage.projection
#audit_axioms GroupApproximation.MFCamouflage.blackHole_injective
#audit_axioms GroupApproximation.MFCamouflage.productVertex_injective
#audit_axioms GroupApproximation.MFCamouflage.defect_ne_one
