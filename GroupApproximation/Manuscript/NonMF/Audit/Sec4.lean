import GroupApproximation.Meta.AxiomGuard
import GroupApproximation.Algebra.MappingTelescope
import GroupApproximation.Analysis.AmenableExtensionAmenableTrace
import GroupApproximation.Analysis.AmenableExtensionSentences
import GroupApproximation.Analysis.LocallyRFByIntAmenableTrace
import GroupApproximation.Analysis.MaximalGroupCStar
import GroupApproximation.Analysis.MaximalGroupCStarTrace
import GroupApproximation.Analysis.QuasidiagonalTrace
import GroupApproximation.Analysis.TikuisisWhiteWinterCore
import GroupApproximation.Manuscript.NinetyNineProblems.ProblemXGroups
import GroupApproximation.Manuscript.NonMF.AffineDoublingLiteralModel
import GroupApproximation.Manuscript.NonMFSentences.AmenableTraceSentencesB
import GroupApproximation.Manuscript.OneSidedMFRadical.AffineCliffordTrace
import GroupApproximation.Manuscript.OneSidedMFRadical.FactorizationTraceSentences
import GroupApproximation.Monsters.ExplicitIntegralLinearModel
import GroupApproximation.Monsters.ExplicitLinearModel
import GroupApproximation.Sofic.AffineHNNBaseRealization
import GroupApproximation.Sofic.CliffordConstructionSentences
import GroupApproximation.Sofic.CliffordLampGroup
import GroupApproximation.Sofic.CliffordWitnessDirectDefect
import GroupApproximation.Sofic.CliffordWitnessHSRemark
import GroupApproximation.Sofic.CliffordWitnessLocallyRFByInt
import GroupApproximation.Sofic.CliffordWitnessSoficPrinted
import GroupApproximation.Sofic.CliffordWitnessSoficSentences
import GroupApproximation.Sofic.CommutingLampCollapse
import GroupApproximation.Sofic.MFTraceCoronaBridge
import GroupApproximation.Sofic.MappingTelescopeFiniteOrbits
import GroupApproximation.Sofic.MarkedCompressionGroup
import GroupApproximation.Sofic.SoficByAmenablePermanence
import GroupApproximation.Sofic.SoficDirectedUnion

/-!
# Audit gate: `sec:amenable-nonqd`

`non_mf_groups_exist.tex` lines 1324–1620.

Every census row in this range with status `formalized` or `definition` names Lean
declarations, and so does every structural or attribution row that makes a mathematical
claim.  Each declaration is audited below, so a widened axiom closure, or a declaration
that has been lost or renamed, becomes a build error in this module.

* `#audit_closed_axioms` is used on named-proposition endpoints and on other theorems
  whose type is not a leading binder.
* `#audit_axioms` is used on every other carrier: definitions, and sentence-level lemmas
  whose hypotheses are the printed setup or the conclusions of earlier sentences.

Each group of lines names its census row ids and tex line, then the printed sentence as
the census records it.  When a row names only a `Printed…` proposition, the theorem that
proves it follows.  A `definition` row whose census entry names no declaration gets the
object it names here, and the row correction goes to the census lane.

Rows with status `partial` belong to lanes still working on the walls and are not gated
here.  Structural, attribution and history rows that assert nothing name no declaration.
-/

/-! ## L1327 `3f53897704ba`, `4daee6130a7d` (definition): maps $\phi_n\colon A\to M_{d_n}(\C)$
such that -/

#audit_axioms GroupApproximation.Quasidiagonal.IsAmenableTrace
#audit_axioms GroupApproximation.Quasidiagonal.AmenableTraceModel

/-! ## L1339 `f02bfca27b23` (definition): It is \emph{quasidiagonal} if the first limit holds in
operator norm instead of normalized Hilbert--Schmidt norm, with the same trace
convergence. -/

#audit_axioms GroupApproximation.Quasidiagonal.IsQuasidiagonalTrace
#audit_axioms GroupApproximation.Quasidiagonal.QuasidiagonalTraceModel

/-! ## L1342 `c9da12b3f699` (definition): The canonical trace $\tau_G$ is determined by -/

#audit_axioms GroupApproximation.canonicalMaximalTrace_generator_one
#audit_axioms GroupApproximation.canonicalMaximalTrace_generator_of_ne_one

/-! ## L1342 `ca353970e9e3` (definition): For a countable group $G$, let $u_g$ denote the
canonical unitary in $C^*_{\max}(G)$. -/

#audit_axioms GroupApproximation.maximalGroupCStarGenerator

/-! ## L1351 `01d34ed18b0a`: If $G$ is not MF, then its canonical trace $\tau_G$ on
$C^*_{\max}(G)$ is not quasidiagonal. In particular, if $\tau_G$ is amenable, then
$\tau_G$ is … -/

#audit_closed_axioms GroupApproximation.NinetyNineProblems.manuscriptCanonicalMaximalTraceNotIsQuasidiagonalTraceOfNotIsOperatorMF
#audit_axioms GroupApproximation.NinetyNineProblems.canonicalMaximalTrace_amenable_not_isQuasidiagonalTrace_of_not_isOperatorMF

/-! ## L1360 `0fbd72617dcb`: Asymptotic multiplicativity in operator norm makes
$a\mapsto[(\phi_n(a))_n]$ a unital $*$-homomorphism $\Phi\colon C^*_{\max}(G)\to\mathcal … -/

#audit_axioms GroupApproximation.ShulmanTrace.MFTraceModel.coronaHom

/-! ## L1360 `1c2804634e53`: If $\Phi(u_g)=1$, then $\opnorm{\phi_n(u_g)-1}\to0$, so
$\tr_{d_n}(\phi_n(u_g))\to1$, while $\tr_{d_n}(\phi_n(u_g))\to\tau_G(u_g)$; so $g=1$. -/

#audit_axioms GroupApproximation.ShulmanTrace.exists_injective_coronaUnitaryHom

/-! ## L1360 `53f02dc594db`: Hence $g\mapsto\Phi(u_g)$ is a corona homomorphism injective on $G$,
and $G$ is MF, contrary to the hypothesis. -/

#audit_axioms GroupApproximation.ShulmanTrace.exists_injective_coronaUnitaryHom
#audit_axioms GroupApproximation.FactorizationTraceSentences.manuscriptSentence_quasidiagonalGivesMF

/-! ## L1360 `fa19477760b9`: Suppose that $\tau_G$ is quasidiagonal, with u.c.p.\ maps
$\phi_n\colon C^*_{\max}(G)\to M_{d_n}(\C)$ as in the definition. -/

#audit_axioms GroupApproximation.FactorizationTraceSentences.manuscriptSentence_quasidiagonalModel

/-! ## L1371 `a817c6ae86c9` (definition): A group $N$ is \emph{locally residually finite} if each
of its finitely generated subgroups is residually finite. -/

#audit_axioms GroupApproximation.LocallyRFByIntAmenableTrace.IsLocallyResiduallyFinite

/-! ## L1376 `0bd25ebcbeac`, `fd8372f71c2d`: Then the canonical trace of $C^*_{\max}(N)$ is
quasidiagonal, and the canonical trace of $C^*_{\max}(G)$ is amenable. -/

#audit_closed_axioms GroupApproximation.AmenableExtensionTrace.manuscriptPrintedAmenableExtensionTrace

/-! ## L1384 `94ebd1377c15`, `a97f0ab46cd9`: For $g\in \Sigma$ and $x\in F$ put -/

#audit_axioms GroupApproximation.AmenableExtensionSentences.manuscriptSentence_cocycleValues

/-! ## L1384 `d47b613bb096` (structural): The models are compressions of a quasi-regular
representation of $G$ to a finite set of cosets indexed by a F\o lner set of $A$ and a
finite quotient … -/

#audit_axioms GroupApproximation.AmenableExtensionSentences.manuscriptSentence_compressionUCPAndTranslation
#audit_axioms GroupApproximation.AmenableExtensionSentences.manuscriptSentence_rankBoundGivesHS

/-! ## L1395 `30eb3e57ac10`: The cosets $\sigma(x)r_q\Lambda$, $x\in F$, $q\in \Delta$, are
pairwise distinct, since equality forces $x=x'$ in $A$ and then $q=q'$; let $T$ be … -/

#audit_axioms GroupApproximation.AmenableExtensionSentences.manuscriptSentence_cosetsDistinct
#audit_axioms GroupApproximation.AmenableExtensionSentences.manuscriptSentence_compressionUCPAndTranslation

/-! ## L1395 `6e563dbca22b`: The subgroup $N_0$ generated by these finitely many elements is
residually finite; choose a finite quotient $\theta\colon N_0\to \Delta$ with … -/

#audit_axioms GroupApproximation.AmenableExtensionSentences.manuscriptSentence_cocyclePacketSeparates

/-! ## L1395 `da2fd300384a`: This map is u.c.p., and for $g\in \Sigma$ and $\bar gx\in F$, -/

#audit_axioms GroupApproximation.AmenableExtensionSentences.manuscriptSentence_compressionUCPAndTranslation

/-! ## L1408 `89bc31ec5034`: So for $g,h\in \Sigma$ the identity
$\Phi(u_{gh})-\Phi(u_g)\Phi(u_h)=\Pi\lambda(g)(1-\Pi)\lambda(h)\Pi$ and the rank of
$(1-\Pi)\lambda(h)\Pi$, at … -/

#audit_axioms GroupApproximation.AmenableExtensionSentences.manuscriptSentence_rankBoundGivesHS

/-! ## L1416 `1ea7f92c66a1`: The normalized trace of $\Phi(u_g)$ is the fraction of points of $T$
fixed by $g$, and for $g\in \Sigma\setminus\{1\}$ it is zero: if $\bar g\ne1$, … -/

#audit_axioms GroupApproximation.AmenableExtensionSentences.manuscriptSentence_traceIsFixedPointFraction

/-! ## L1416 `b77ceccea9ed`: Taking F\o lner sets with $|\{x\in F:\bar hx\notin F\}|/|F|\to0$ for
the finitely many $h\in \Sigma$, along an exhaustion of $G$ by finite sets … -/

#audit_axioms GroupApproximation.AmenableExtensionSentences.manuscriptSentence_folnerLimitsExtend

/-! ## L1428 `23d58dbda4bf`: For the canonical trace of $C^*_{\max}(N)$, run the same
construction with $N$ in place of $G$, $A=1$, and $F=\{1\}$: no boundary term appears, so
… -/

#audit_axioms GroupApproximation.AmenableExtensionSentences.manuscriptSentence_stagePacketSeparates
#audit_axioms GroupApproximation.AmenableExtensionSentences.manuscriptSentence_stageCompressionUCP
#audit_axioms GroupApproximation.AmenableExtensionSentences.manuscriptSentence_stageTraceZero
#audit_axioms GroupApproximation.AmenableExtensionSentences.manuscriptSentence_stageLimitsExtend

/-! ## L1435 `60898a519f4f` (definition): Let $\Gamma$ be a countable group with
property~\textup{(T)}, let $\alpha\colon\Gamma\to\Gamma$ be injective but not surjective,
and choose … -/

#audit_axioms GroupApproximation.CliffordWitnessDirectDefect.PrintedCliffordWitnessNotIsOperatorMF
#audit_closed_axioms GroupApproximation.CliffordWitnessDirectDefect.manuscriptCliffordWitnessNotIsOperatorMF

/-! ## L1435 `8e53d32e3fb8` (structural): We now construct a group to which
Theorem~\ref{thm:compression-criterion} applies through a finite central subgroup: its
intrinsic defect subgroup … -/

#audit_axioms GroupApproximation.AmenableTraceSentencesB.manuscriptSentence_defectFactorization
#audit_axioms GroupApproximation.CliffordWitnessDirectDefect.signSubgroup_le_printedDefect

/-! ## L1435 `c180c0186454` (definition): Put -/

#audit_axioms GroupApproximation.MappingTelescope.Telescope
#audit_axioms GroupApproximation.MarkedCompression.Vertical

/-! ## L1448 `08844a3bdb91` (definition): Put $X=V/\Gamma$, the left-coset space. -/

#audit_axioms GroupApproximation.MarkedCompression.Cosets
#audit_axioms GroupApproximation.MarkedCompression.rootCoset

/-! ## L1448 `86ba78fb0d96`: The Clifford lamp group $\operatorname{Cl}(X)$ is the group with
generators $\varepsilon$ and $c_x$, $x\in X$, and relations -/

#audit_axioms GroupApproximation.CliffordConstructionSentences.manuscriptSentence_cliffordLampPresentation

/-! ## L1448 `d5c52ca23af0`: where $tgt^{-1}=\alpha(g)$ on the level-zero copy of $\Gamma$, so
that $V$ is the ascending HNN extension of $\Gamma$ along $\alpha$ and … -/

#audit_axioms GroupApproximation.CliffordConstructionSentences.manuscriptSentence_hnnExtension

/-! ## L1458 `4cbf47e489a6` (structural): To see that $\varepsilon\ne1$, fix a total order on
$X$, let $\F_2^{(X)}$ be the $\F_2$-vector space of finitely supported functions
$X\to\F_2$, and … -/

#audit_axioms GroupApproximation.CliffordLamp.crossing

/-! ## L1458 `dc43ec6b23ed`: Since $B$ is bilinear, -/

#audit_axioms GroupApproximation.CliffordConstructionSentences.manuscriptSentence_signedModelGroupLaw

/-! ## L1464 `1fab0dcc8e88`: So $\varepsilon\mapsto(1,0)$, $c_x\mapsto(0,\delta_x)$ defines a
homomorphism $\operatorname{Cl}(X)\to\F_2\times\F_2^{(X)}$. -/

#audit_axioms GroupApproximation.CliffordConstructionSentences.manuscriptSentence_toModelHomomorphism

/-! ## L1464 `4704b74b6c8e`: is a group law on $\F_2\times\F_2^{(X)}$, in which $(1,0)$ is a
central involution, each $(0,\delta_x)$ is an involution, and for $x\ne y$ exactly … -/

#audit_axioms GroupApproximation.CliffordConstructionSentences.manuscriptSentence_signedModelGroupLaw

/-! ## L1464 `b9ca7188b1f5`: The relations let us write every element of $\operatorname{Cl}(X)$
as -/

#audit_axioms GroupApproximation.CliffordConstructionSentences.manuscriptSentence_cliffordLampNormalForm

/-! ## L1475 `407925e64c6c`: and this word maps to $(a,\delta_{x_1}+\cdots+\delta_{x_r})$, so the
expression is unique and the homomorphism is an isomorphism. -/

#audit_axioms GroupApproximation.CliffordConstructionSentences.manuscriptSentence_cliffordLampNormalForm

/-! ## L1475 `51284d178433`: In particular, for a finite subset $Y\subseteq X$, the subgroup
generated by $\varepsilon$ and the $c_y$ with $y\in Y$ has order $2^{|Y|+1}$, so … -/

#audit_axioms GroupApproximation.CliffordConstructionSentences.manuscriptSentence_cliffordLampCountableLocallyFinite

/-! ## L1475 `5306701b688c`: In this way $V$ acts on $\operatorname{Cl}(X)$ through its action on
$X$, and we put -/

#audit_axioms GroupApproximation.CliffordConstructionSentences.manuscriptSentence_verticalActsOnLamp

/-! ## L1475 `ad753104ce33`: The relations are invariant under permutations of $X$, so every
permutation of $X$ induces an automorphism of $\operatorname{Cl}(X)$ that permutes … -/

#audit_axioms GroupApproximation.CliffordConstructionSentences.manuscriptSentence_permutationAutomorphism

/-! ## L1475 `c41bad22d29b`: Killing $\varepsilon$ leaves $\F_2^{(X)}\cong\bigoplus_XC_2$, so
$\operatorname{Cl}(X)$ is a central extension of $\bigoplus_XC_2$ by $C_2$, and $W$ … -/

#audit_axioms GroupApproximation.AmenableTraceSentencesB.manuscriptSentence_cliffordLampKillSignCentralExtension
#audit_axioms GroupApproximation.AmenableTraceSentencesB.manuscriptSentence_wCentralExtensionOfWreath

/-! ## L1494 `7732f82e8623`: More precisely, every homomorphism from $W$ to an MF group kills
$\varepsilon$. -/

#audit_closed_axioms GroupApproximation.CliffordWitnessDirectDefect.manuscriptCliffordWitnessNotIsOperatorMF
#audit_closed_axioms GroupApproximation.CliffordWitnessDirectDefect.manuscriptMapSignEqOneOfIsOperatorMFTarget

/-! ## L1494 `8abb5071b65b`: The group $W$ is not MF. -/

#audit_closed_axioms GroupApproximation.CliffordWitnessDirectDefect.manuscriptCliffordWitnessNotIsOperatorMF

/-! ## L1501 `013d2e0e8b4a`: So Theorem~\ref{thm:compression-criterion} applies to the countable
group $W$ with $L=\Gamma$ and $K=\langle\varepsilon\rangle$: every homomorphism … -/

#audit_closed_axioms GroupApproximation.CliffordWitnessDirectDefect.manuscriptMapSignEqOneOfIsOperatorMFTarget

/-! ## L1501 `177456a78260`: Identify $\Gamma$ with its level-zero copy in $V\le W$, and let $c$
be the lamp at the root coset $\Gamma\in X$; it centralizes $\Gamma$, which fixes … -/

#audit_axioms GroupApproximation.AmenableTraceSentencesB.manuscriptSentence_rootLampCentralizesFixesCoset

/-! ## L1501 `24b5330b38b0`: The subgroup $\langle\varepsilon\rangle$ is central, so normal, and
it is finite, so it has property~\textup{(T)}. -/

#audit_axioms GroupApproximation.AmenableTraceSentencesB.manuscriptSentence_signSubgroupCentralNormalFiniteHasT

/-! ## L1501 `28740c0c5a93`: In particular, $W$ is not MF\@. -/

#audit_closed_axioms GroupApproximation.CliffordWitnessDirectDefect.manuscriptCliffordWitnessNotIsOperatorMF

/-! ## L1501 `91502a70ae59`: Then $d=[x,a]=xy$ and $d^2=xyxy=[x,y]=\varepsilon$, and
$d=[tct^{-1},a]$ is a generator of $\mathfrak D_W(\Gamma)$, since $t\Gamma
t^{-1}\le\Gamma$, … -/

#audit_axioms GroupApproximation.AmenableTraceSentencesB.manuscriptSentence_defectFactorization
#audit_axioms GroupApproximation.CliffordWitnessDirectDefect.pointDefect_mem_printedDefect
#audit_axioms GroupApproximation.CliffordWitnessDirectDefect.stable_mem_compressionSet
#audit_axioms GroupApproximation.CliffordWitnessDirectDefect.lamp_mem_centralizer

/-! ## L1501 `a0acefd07ec1`: Then $tct^{-1}$ is the lamp at $t\Gamma$ and $a(tct^{-1})a^{-1}$ is
the lamp at $at\Gamma$. -/

#audit_axioms GroupApproximation.CliffordConstructionSentences.manuscriptSentence_conjugatedLampsAtCosets

/-! ## L1501 `b33af3eb4b3c`: So $\langle\varepsilon\rangle\le\mathfrak D_W(\Gamma)$. -/

#audit_axioms GroupApproximation.CliffordWitnessDirectDefect.signSubgroup_le_printedDefect

/-! ## L1501 `dba28fb94e6d`: These cosets are distinct, because $t\Gamma=at\Gamma$ would mean
$a\in t\Gamma t^{-1}=\alpha(\Gamma)$; so $x=tct^{-1}$ and $y=axa^{-1}$ are distinct … -/

#audit_axioms GroupApproximation.CliffordConstructionSentences.manuscriptSentence_movedCosetsDistinct
#audit_axioms GroupApproximation.AmenableTraceSentencesB.manuscriptSentence_distinctInvolutionsCommutatorSign

/-! ## L1521 `a2ba60db6a3b`: Suppose in addition that $\Gamma$ is residually finite and that
$[\Gamma:\alpha(\Gamma)]<\infty$. -/

#audit_closed_axioms GroupApproximation.AmenableTraceTheorem.manuscriptCliffordLocallyRF
#audit_closed_axioms GroupApproximation.CliffordWitnessLocallyRFByInt.manuscriptAmbientEquivShiftKernelForByInt
#audit_closed_axioms GroupApproximation.CliffordWitnessLocallyRFByInt.manuscriptShiftKernelForIsLocallyResiduallyFinite

/-! ## L1527 `93aa71e6b818`, `a0abcf4e0a16`: where $W_0$ is locally residually finite. -/

#audit_closed_axioms GroupApproximation.AmenableTraceTheorem.manuscriptCliffordLocallyRF

/-! ## L1534 `9355c08e7f2b`: Reassociating the semidirect products yields -/

#audit_closed_axioms GroupApproximation.CliffordWitnessLocallyRFByInt.witnessGroupEquivShiftKernelByInt
#audit_axioms GroupApproximation.AmenableTraceTheorem.manuscriptSentence_reassociation

/-! ## L1539 `404ff3b063bf`: Hence the stabilizer in $\Gamma_n$ of every point of $X=V/\Gamma$
has finite index, and every $\Gamma_n$-orbit in $X$ is finite. -/

#audit_axioms GroupApproximation.AmenableTraceTheorem.manuscriptSentence_stabilizerAndOrbitFinite

/-! ## L1539 `4cdae54eba21`: Since $[\Gamma:\alpha(\Gamma)]<\infty$, each $\Gamma_n$ has finite
index in $\Gamma_{n+1}$; every element of $T_\alpha$ lies in some $\Gamma_m$, and … -/

#audit_axioms GroupApproximation.AmenableTraceTheorem.manuscriptSentence_commensuration
#audit_axioms GroupApproximation.MappingTelescopeFiniteOrbits.t_conj_base_eq_compressed

/-! ## L1539 `bc2d73bb124a` (definition): For $n\ge0$, write $\Gamma_n=t^{-n}\Gamma t^n$ for the
image of the $n$th copy of $\Gamma$ in $T_\alpha$. -/

#audit_axioms GroupApproximation.MappingTelescope.level
#audit_axioms GroupApproximation.MappingTelescopeFiniteOrbits.verticalLevel

/-! ## L1548 `a60285a8682e`: Then $Y$ is finite and $\Gamma_n$-invariant, and the finite subset
is contained in -/

#audit_axioms GroupApproximation.AmenableTraceTheorem.manuscriptSentence_finiteInvariantSubgroup

/-! ## L1548 `e4ebdec3bbab` (definition): Let $Y$ be the union of the $\Gamma_n$-orbits of these
finitely many $x$. -/

#audit_axioms GroupApproximation.AmenableTraceTheorem.manuscriptSentence_finiteInvariantSubgroup

/-! ## L1548 `edc038ff7b5f`: A finite subset of $W_0$ involves only finitely many lamps $c_x$,
and its $T_\alpha$-coordinates lie in one $\Gamma_n$. -/

#audit_axioms GroupApproximation.AmenableTraceTheorem.manuscriptSentence_finiteSubsetOneLevel

/-! ## L1555 `2a24a52c111f`: where $C_Y=\langle\varepsilon,c_y:y\in Y\rangle$ is finite by the
normal form above. -/

#audit_axioms GroupApproximation.AmenableTraceTheorem.manuscriptSentence_finiteInvariantSubgroup

/-! ## L1555 `508294d77cb5`: Therefore every finitely generated subgroup of $W_0$ is residually
finite, hence sofic. -/

#audit_axioms GroupApproximation.AmenableTraceTheorem.manuscriptSentence_locallyResiduallyFinite
#audit_axioms GroupApproximation.AmenableTraceTheorem.manuscriptSentence_fgSubgroupSofic

/-! ## L1555 `675969466d3b`, `9f522f4b56dd`, `ab3b4185d7d4`, `bba6a4ecce85`: This semidirect
product is residually finite. -/

#audit_axioms GroupApproximation.AmenableTraceTheorem.manuscriptSentence_semidirectResiduallyFinite

/-! ## L1566 `2c614717a212`: Soficity passes to directed unions and to extensions with amenable
quotient~\cite[Theorem~1]{ElekSzabo}, so $W$ is sofic. -/

#audit_axioms GroupApproximation.isSofic_of_every_finset_mem_sofic_subgroup
#audit_axioms GroupApproximation.isSofic_of_increasing_union
#audit_axioms GroupApproximation.SoficByAmenablePermanence.manuscriptSoficOfSoficKerOfAmenableQuotient
#audit_axioms GroupApproximation.AmenableTraceTheorem.manuscriptSentence_wSoficMechanism

/-! ## L1566 `8cde0b44b52f`: The group $W_0$ is their directed union, and $W/W_0\cong\mathbb Z$
is amenable. -/

#audit_closed_axioms GroupApproximation.AmenableTraceTheorem.manuscriptSentence_quotientAmenable

/-! ## L1566 `a998ccfa2015`: By Proposition~\ref{prop:locally-rf-by-z-trace}, applied to the
extension $1\to W_0\to W\to\mathbb Z\to1$, the canonical trace of $C^*_{\max}(W_0)$ … -/

#audit_axioms GroupApproximation.AmenableTraceTheorem.manuscriptSentence_traceConclusions

/-! ## L1566 `f1f1ba4ba319`: Proposition~\ref{prop:clifford-self-embedding} shows that it is not
MF. -/

#audit_axioms GroupApproximation.AmenableTraceTheorem.manuscriptSentence_notMF

/-! ## L1577 `42ae3f886537`: So the collapse of Corollary~\ref{cor:defect-hs} fails for
asymptotic representations in normalized Hilbert--Schmidt norm, although $\varepsilon$ is
… -/

#audit_closed_axioms GroupApproximation.CliffordWitnessHSRemark.manuscriptSentence_hsCollapseFails
#audit_closed_axioms GroupApproximation.CliffordWitnessHSRemark.manuscriptSentence_noSoficCompressionCriterion

/-! ## L1577 `86d7bbda9474`: The permutation matrices $V_n$ of a sofic approximation of $W$
satisfy $\hsnorm{V_n(gh)-V_n(g)V_n(h)}\to0$, while … -/

#audit_closed_axioms GroupApproximation.CliffordWitnessHSRemark.manuscriptSentence_soficPermutationModelsHS
#audit_axioms GroupApproximation.CliffordWitnessHSRemark.tendsto_hsNorm_modelUnitary_mul
#audit_axioms GroupApproximation.CliffordWitnessHSRemark.tendsto_hsNorm_modelUnitary_sub_one
#audit_axioms GroupApproximation.CliffordWitnessHSRemark.tendsto_movedFraction_of_ne_one

/-! ## L1589 `3229365c29c6` (definition): For a concrete instance, take -/

#audit_axioms GroupApproximation.ExplicitLinearModel.gammaBar
#audit_axioms GroupApproximation.AffineHNNBase.affUnit
#audit_axioms GroupApproximation.AffineHNNBase.affUnit_val
#audit_axioms GroupApproximation.Manuscript.NonMF.AffineDoublingLiteralModel.PrintedGammaBarAffine
#audit_closed_axioms GroupApproximation.Manuscript.NonMF.AffineDoublingLiteralModel.printedGammaBarAffine

/-! ## L1598 `77028123cdd6`: It is residually finite, since reduction modulo a suitable integer
separates any two distinct integral matrices, and it has … -/

#audit_closed_axioms GroupApproximation.ExplicitIntegralLinearModel.gammaBar_residuallyFinite
#audit_closed_axioms GroupApproximation.CommutingLampCollapse.gammaBar_hasKazhdanPropertyT

/-! ## L1598 `e947a3d4f4a1` (definition): Let -/

#audit_axioms GroupApproximation.ExplicitLinearModel.dU
#audit_axioms GroupApproximation.ExplicitLinearModel.conjD
#audit_axioms GroupApproximation.Manuscript.NonMF.AffineDoublingLiteralModel.PrintedConjDDefinition
#audit_closed_axioms GroupApproximation.Manuscript.NonMF.AffineDoublingLiteralModel.printedConjDDefinition

/-! ## L1608 `7f667d9f1cb7`: So the preceding construction applies to $\bar\Gamma$, $\alpha$ and
$a$. -/

#audit_closed_axioms GroupApproximation.AmenableTraceTheorem.manuscriptAffineCliffordConclusions
#audit_closed_axioms GroupApproximation.AmenableTraceTheorem.manuscriptSentence_theorem4Application

/-! ## L1608 `80c65e0771e4`: so that $\alpha(v,A)=(2v,A)$. -/

#audit_axioms GroupApproximation.CliffordConstructionSentences.manuscriptSentence_alphaDoublesTranslation
#audit_axioms GroupApproximation.Manuscript.NonMF.AffineDoublingLiteralModel.PrintedConjDDoublesTranslation
#audit_closed_axioms GroupApproximation.Manuscript.NonMF.AffineDoublingLiteralModel.printedConjDDoublesTranslation

/-! ## L1608 `8c17c33ec225`: Translation $a$ by the first standard basis vector lies outside
$\alpha(\bar\Gamma)$. -/

#audit_closed_axioms GroupApproximation.AmenableTraceSentencesB.manuscriptSentence_concreteInstanceDoubling
#audit_closed_axioms GroupApproximation.AmenableTraceTheorem.manuscriptAffineCliffordHypotheses

/-! ## L1608 `c48c7da870a2`: This is injective, and its image consists of the affine matrices
whose translation coordinates are all even, so $[\bar\Gamma:\alpha(\bar\Gamma)]=8$. -/

#audit_closed_axioms GroupApproximation.AmenableTraceSentencesB.manuscriptSentence_concreteInstanceDoubling
#audit_axioms GroupApproximation.Manuscript.NonMF.AffineDoublingLiteralModel.PrintedConjDRangeEvenTranslations
#audit_closed_axioms GroupApproximation.Manuscript.NonMF.AffineDoublingLiteralModel.printedConjDRangeEvenTranslations

/-! ## L1615 `4ce81a3db24b`: Apply Proposition~\ref{prop:clifford-locally-rf} to $\bar\Gamma$,
$\alpha$, and $a$. -/

#audit_closed_axioms GroupApproximation.AmenableTraceTheorem.manuscriptSentence_theorem4Application
