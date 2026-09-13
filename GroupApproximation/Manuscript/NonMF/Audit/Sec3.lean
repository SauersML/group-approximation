import GroupApproximation.Meta.AxiomGuard
import GroupApproximation.Algebra.ExchangeRing
import GroupApproximation.Algebra.FinitaryLinearBinaryPower
import GroupApproximation.Algebra.FinitaryLinearBinarySLUnion
import GroupApproximation.Algebra.FinitaryLinearFiniteRank
import GroupApproximation.Algebra.FinitaryLinearTransvections
import GroupApproximation.Algebra.LaurentBinaryLinearMF
import GroupApproximation.Algebra.PeirceBlockFactorization
import GroupApproximation.Algebra.PeirceElementaryFactorization
import GroupApproximation.Algebra.PreusserSandwichExchange
import GroupApproximation.Algebra.PurelyInfiniteSimpleRing
import GroupApproximation.Analysis.ReducedGroupCStarMFAlgebra
import GroupApproximation.KOne.AlgebraicKOne
import GroupApproximation.KOne.ClassicalKOne
import GroupApproximation.KOne.LeavittKOneScalarKernel
import GroupApproximation.KOne.LeavittKOneScalarQuotient
import GroupApproximation.KOne.StableWhitehead
import GroupApproximation.Leavitt.AryPurelyInfinite
import GroupApproximation.Leavitt.BinaryLeavittSimple
import GroupApproximation.Leavitt.CongruenceSubgroups
import GroupApproximation.Leavitt.ElementaryWeylMonomial
import GroupApproximation.Leavitt.ExchangePrerequisite
import GroupApproximation.Leavitt.LeavittCenter
import GroupApproximation.Leavitt.OneSidedCompressor
import GroupApproximation.Leavitt.OneSidedCompressorDefect
import GroupApproximation.Leavitt.OneSidedInverse
import GroupApproximation.Leavitt.PreusserAssembly
import GroupApproximation.Leavitt.ProperlyInfiniteUnit
import GroupApproximation.Leavitt.RankTwoNormalGeneration
import GroupApproximation.Leavitt.UniversalOneSidedPairRing
import GroupApproximation.Manuscript.NonMF.RingCompressionCellGeneral
import GroupApproximation.Manuscript.NonMFSentences.BinaryExampleSentences
import GroupApproximation.Manuscript.NonMFSentences.CountableAbelianMFPrintedRoute
import GroupApproximation.Manuscript.NonMFSentences.EJZCitationSentences
import GroupApproximation.Manuscript.NonMFSentences.FullDefectAllRanksSentences
import GroupApproximation.Manuscript.NonMFSentences.FullDefectCornerRemark
import GroupApproximation.Manuscript.NonMFSentences.HeadlineCitationSentences
import GroupApproximation.Manuscript.NonMFSentences.LeavittKOneFormulaSentences
import GroupApproximation.Manuscript.NonMFSentences.LeavittKOneQuotientEvaluations
import GroupApproximation.Manuscript.NonMFSentences.LeavittMFQuotientBothInclusions
import GroupApproximation.Manuscript.NonMFSentences.LeavittMFQuotientDiagonalSentence
import GroupApproximation.Manuscript.NonMFSentences.LeavittMFQuotientSentences
import GroupApproximation.Manuscript.NonMFSentences.MFQuotientUnitsCongruencePrinted
import GroupApproximation.Manuscript.NonMFSentences.MFQuotientUnitsCornerUnits
import GroupApproximation.Manuscript.NonMFSentences.MFQuotientUnitsItemA
import GroupApproximation.Manuscript.NonMFSentences.MFQuotientUnitsItemB
import GroupApproximation.Manuscript.NonMFSentences.MFQuotientUnitsOffLastCorner
import GroupApproximation.Manuscript.NonMFSentences.MFQuotientUnitsSteinberg
import GroupApproximation.Manuscript.NonMFSentences.MFQuotientUnitsStepOnePrinted
import GroupApproximation.Manuscript.NonMFSentences.OneSidedCorollarySentences
import GroupApproximation.Manuscript.NonMFSentences.OneSidedSentences
import GroupApproximation.Manuscript.NonMFSentences.RankTwoPrintedSteps
import GroupApproximation.Manuscript.NonMFSentences.UniversalRingSentences
import GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingEJZUnconditional
import GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingProperIsometry
import GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingRankTwo
import GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingSentences
import GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingUnconditional
import GroupApproximation.Manuscript.OneSidedMFRadical.JacobsonBlockAction
import GroupApproximation.Manuscript.OneSidedMFRadical.JacobsonFiniteMatrices
import GroupApproximation.Manuscript.OneSidedMFRadical.JacobsonKernelFinitary
import GroupApproximation.Manuscript.OneSidedMFRadical.JacobsonRankFourSentences
import GroupApproximation.Manuscript.OneSidedMFRadical.JacobsonRankTwoInert
import GroupApproximation.Manuscript.OneSidedMFRadical.KhanhThanhDecompositionClosed
import GroupApproximation.Manuscript.OneSidedMFRadical.KhanhThanhDiagonalDecomposition
import GroupApproximation.Manuscript.OneSidedMFRadical.MFHomKernel
import GroupApproximation.Manuscript.OneSidedMFRadical.MFQuotientCanonicalKOne
import GroupApproximation.Manuscript.OneSidedMFRadical.MFQuotientUnitsAGPProof
import GroupApproximation.Manuscript.OneSidedMFRadical.MFQuotientUnitsKappaProof
import GroupApproximation.Manuscript.OneSidedMFRadical.MFQuotientUnitsSentences
import GroupApproximation.Manuscript.OneSidedMFRadical.RankDescentPrintedLemmas
import GroupApproximation.Manuscript.OneSidedMFRadical.RankFourCompressionCellPrinted
import GroupApproximation.Manuscript.OneSidedMFRadical.RankFourEJZInstance
import GroupApproximation.Manuscript.OneSidedMFRadical.RankFourEndpoints
import GroupApproximation.Manuscript.OneSidedMFRadical.RankFourSimplicity
import GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveSimplicitySentences
import GroupApproximation.Manuscript.OneSidedMFRadical.TorsionComplementaryIdempotents
import GroupApproximation.Manuscript.OneSidedMFRadical.TorsionComplementaryIdempotentsDefect
import GroupApproximation.Manuscript.OneSidedMFRadical.TorsionComplementaryIdempotentsDiagonal
import GroupApproximation.Manuscript.OneSidedMFRadical.TorsionComplementaryIdempotentsMatrixUnits
import GroupApproximation.Manuscript.OneSidedMFRadical.TorsionComplementaryIdempotentsSentences
import GroupApproximation.Manuscript.OneSidedMFRadical.TorsionComplementaryIdempotentsSignedPermutations
import GroupApproximation.Manuscript.OneSidedMFRadical.UnitGroupRankDescent
import GroupApproximation.Manuscript.OneSidedMFRadical.UniversalGroupB
import GroupApproximation.Manuscript.OneSidedMFRadical.UniversalGroupSigma

/-!
# Audit gate: `sec:one-sided-inverses`, MF quotients of unit groups

`non_mf_groups_exist.tex` lines 785–1323.

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

/-! ## L788 `19abb698ab4a` (structural): The proof of Theorem~\ref{thm:full-defect-ring} runs in
rank four over the ring $\mathcal C$, with three coordinates for the subgroup
$\EL_3(\mathcal … -/

#audit_closed_axioms GroupApproximation.Manuscript.NonMFSentences.HeadlineCitationSentences.manuscriptSentence_finitelyGeneratedGivesPropertyT
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.RankFourEndpoint.hasKazhdanPropertyT_viaEJZ

/-! ## L788 `3a929e3e1455` (structural): The compressor needs only $ts=1$; the ideal condition on
$1-st$ enters in the last step of the rank-four argument and in the first lemma. -/

#audit_axioms GroupApproximation.OneSidedCompressor.compressor
#audit_axioms GroupApproximation.OneSidedCompressor.compressor_compresses_core

/-! ## L798 `c90393ba6292`, `d269b2fd7294`, `e123b14ddeee`: Conversely, such elements satisfy
$w_0v_0=1$ and $w_1(1-v_0w_0)v_1=1$. -/

#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.RankDescentPrinted.manuscriptTwoCopiesLemma

/-! ## L806 `5870021d2e03` (definition): Put -/

#audit_axioms GroupApproximation.OneSidedCompressor.OneSidedInverse.e
#audit_axioms GroupApproximation.RankDescent.ofFull

/-! ## L806 `9dbe7e587681`: Put $e=1-st$, so that $es=te=0$, and choose $a_j,b_j\in R$, $0\le
j<m$, with $\sum_ja_jeb_j=1$. -/

#audit_axioms GroupApproximation.RankDescent.ofFull

/-! ## L811 `0bbf89803d26`: Conversely, $w_1(1-v_0w_0)v_1=w_1v_1-(w_1v_0)(w_0v_1)=1$. -/

#audit_axioms GroupApproximation.RankDescent.ProperlyInfiniteUnit.w_one_mul_e_mul_v_one

/-! ## L811 `91d76a509a2b`: For all $i,j\ge0$, $et^is^je=\delta_{ij}e$: for $j>i$ the middle
factor is $s^{j-i}$, which $e$ kills on the left, and for $i>j$ it is $t^{i-j}$, … -/

#audit_axioms GroupApproximation.RankDescent.e_mul_t_pow_mul_s_pow_mul_e

/-! ## L811 `f437c7807b77`: So $w_0v_0=t^ms^m=1$, $w_1v_1=\sum_ja_jeb_j=1$,
$w_0v_1=\sum_jt^{m-j}eb_j=0$, and $w_1v_0=\sum_ja_jes^{m-j}=0$. -/

#audit_axioms GroupApproximation.RankDescent.full_w0_mul_v0
#audit_axioms GroupApproximation.RankDescent.full_w1_mul_v1
#audit_axioms GroupApproximation.RankDescent.full_w0_mul_v1
#audit_axioms GroupApproximation.RankDescent.full_w1_mul_v0

/-! ## L820 `29f5f8b37797`, `a7e56a7fbc34`: Let $R$ be a unital ring and let $v,w,a,b\in R$
satisfy $wv=1$, $ba=1$, and $bv=0$. -/

#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.RankDescentPrinted.manuscriptRankTwoNormalGeneration

/-! ## L825 `9aa5019b614f`: normally generates $\EL_2(R)$. -/

#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.RankDescentPrinted.manuscriptRankTwoNormalGeneration

/-! ## L830 `053b6de1fe6b` (definition): Let $N$ be the normal closure of $D$ in $\EL_2(R)$. -/

#audit_axioms GroupApproximation.Manuscript.NonMFSentences.RankTwoPrintedSteps.printedN

/-! ## L830 `717152bfc217`: For $r\in R$, $[D,e_{12}(ar)]=e_{12}((1+vb)ar-ar)=e_{12}(vr)$, since
$ba=1$; so $e_{12}(vR)\le N$. -/

#audit_axioms GroupApproximation.Manuscript.NonMFSentences.RankTwoPrintedSteps.manuscriptSentence_rankTwoCommutatorUpperRoot

/-! ## L830 `828a8cc4992b`: Put $f=1-vw$, an idempotent with $fv=0=wf$. -/

#audit_axioms GroupApproximation.Manuscript.NonMFSentences.RankTwoPrintedSteps.manuscriptSentence_rankTwoIdempotentF

/-! ## L830 `bd35898b630c`: Since $r=vwr+fr$, it remains to put $e_{12}(fR)$ in $N$, and the
involution -/

#audit_axioms GroupApproximation.Manuscript.NonMFSentences.RankTwoPrintedSteps.manuscriptSentence_rankTwoSplitAndReduction

/-! ## L830 `dbdec0d73e03`: The matrix $e_{12}(v)e_{21}(b)e_{12}(-v)$ has rows $(1+vb,\,-vbv)$
and $(b,\,1-bv)$, so for $bv=0$ it is $1+vb&0\\b&1$, and multiplying by … -/

#audit_axioms GroupApproximation.Manuscript.NonMFSentences.RankTwoPrintedSteps.manuscriptSentence_rankTwoConjugateRows
#audit_axioms GroupApproximation.Manuscript.NonMFSentences.RankTwoPrintedSteps.manuscriptSentence_rankTwoGeneratorDiagonal

/-! ## L841 `5e2b45529464`: Put $x=vf$, $y=fw$, $q=vfw$, and $c=1-f-q$, so that $z=x+y+c$. -/

#audit_axioms GroupApproximation.Manuscript.NonMFSentences.RankTwoPrintedSteps.manuscriptSentence_rankTwoDecomposition

/-! ## L841 `69843250783b`: does this by conjugation, since $zf=vf$. -/

#audit_axioms GroupApproximation.RankDescent.zElt_mul_fIdem
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.RankDescentPrinted.manuscriptRankTwoNormalGeneration

/-! ## L841 `a9865697e6f3`: From $wv=1$ and $fv=wf=0$: $x^2=y^2=0$, $xy=q$, $yx=f$, the
idempotents $f$ and $q$ are orthogonal, and $c$ annihilates $x$ and $y$ on both sides; so
… -/

#audit_axioms GroupApproximation.Manuscript.NonMFSentences.RankTwoPrintedSteps.manuscriptSentence_rankTwoMultiplicationTable

/-! ## L841 `c97ce3c374b2`: The factorization -/

#audit_axioms GroupApproximation.Manuscript.NonMFSentences.RankTwoPrintedSteps.manuscriptSentence_rankTwoSixTransvectionWord
#audit_axioms GroupApproximation.Manuscript.NonMFSentences.RankTwoPrintedSteps.manuscriptSentence_rankTwoConjugationIntoN
#audit_axioms GroupApproximation.Manuscript.NonMFSentences.RankTwoPrintedSteps.upperRoot_f_mem_printedN

/-! ## L849 `05233e222ae6`: So $e_{12}(r)=e_{12}(vwr)\,e_{12}(fr)\in N$ for every $r\in R$, and
conjugating by $e_{12}(1)e_{21}(-1)e_{12}(1)$ gives $e_{21}(R)\le N$. -/

#audit_axioms GroupApproximation.Manuscript.NonMFSentences.RankTwoPrintedSteps.manuscriptSentence_rankTwoUpperAndLowerRoots

/-! ## L849 `db1722e32d5d`: puts $h=\operatorname{diag}(z,z)$ in $\EL_2(R)$, and
$he_{12}(fr)h^{-1}=e_{12}(zfrz)=e_{12}(v\,frz)\in N$. -/

#audit_axioms GroupApproximation.RankDescent.involutionDiag_mul_upperRoot
#audit_axioms GroupApproximation.RankDescent.involutionDiag_conj_upperRoot

/-! ## L857 `1eb8329e0e6b`: In $G=\EL_4(R)$ let $L=\EL_3(R)$ occupy coordinates $1,2,3$. -/

#audit_axioms GroupApproximation.OneSidedCompressor.core
#audit_axioms GroupApproximation.OneSidedCompressor.coreIdx

/-! ## L857 `49be74c2726c`: Let $R$ be a unital ring, let $s,t\in R$ satisfy $ts=1$, and put
$e=1-st$. -/

#audit_axioms GroupApproximation.OneSidedCompressor.OneSidedInverse
#audit_axioms GroupApproximation.OneSidedCompressor.compressor
#audit_axioms GroupApproximation.OneSidedCompressor.centralMark

/-! ## L857 `8f9f00fd2f55`: There are $u,c\in G$ with $uLu^{-1}\le L$ and $c\in C_G(L)$ such that -/

#audit_axioms GroupApproximation.OneSidedCompressor.compressor_compresses_core
#audit_axioms GroupApproximation.OneSidedCompressor.centralMark_commute_core
#audit_axioms GroupApproximation.OneSidedCompressor.compressor_conj_centralMark
#audit_axioms GroupApproximation.OneSidedCompressor.defect_eq

/-! ## L866 `f417d06b695f`: Every off-diagonal entry of a matrix in $uLu^{-1}$ has the form $sat$
with $a\in R$. -/

#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.RankFourCompressionCellPrinted.manuscriptRankFourCompressionCell

/-! ## L872 `718cc7b04afd`: For $i=1,2,3$, set -/

#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingSentences.manuscriptSentence_compressorPieceDef
#audit_axioms GroupApproximation.Manuscript.NonMF.RingCompressionCellGeneral.PrintedCompressorPieces
#audit_closed_axioms GroupApproximation.Manuscript.NonMF.RingCompressionCellGeneral.printedCompressorPieces

/-! ## L872 `fa78bbc31649`: Here $e^2=e$ and $es=te=0$. -/

#audit_axioms GroupApproximation.OneSidedCompressor.OneSidedInverse.e_mul_e
#audit_axioms GroupApproximation.OneSidedCompressor.OneSidedInverse.e_mul_s
#audit_axioms GroupApproximation.OneSidedCompressor.OneSidedInverse.t_mul_e

/-! ## L876 `f52624ced12a`: Its block on coordinates $(i,4)$ is $s&e\\0&t$, so
$u=u_3u_2u_1\in\EL_4(R)$ is the matrix -/

#audit_axioms GroupApproximation.OneSidedCompressor.compressorPiece_val
#audit_axioms GroupApproximation.OneSidedCompressor.compressor
#audit_axioms GroupApproximation.OneSidedCompressor.compressor_val

/-! ## L888 `8ed7601a0e35`: For $1\le i\ne j\le3$ and $a\in R$, -/

#audit_axioms GroupApproximation.OneSidedCompressor.compressor_conj_root

/-! ## L888 `c0383f82a141`: invertible as a product of elementary matrices. -/

#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingSentences.manuscriptSentence_compressorInvertible
#audit_axioms GroupApproximation.Manuscript.NonMF.RingCompressionCellGeneral.PrintedCompressorInvertible
#audit_closed_axioms GroupApproximation.Manuscript.NonMF.RingCompressionCellGeneral.printedCompressorInvertible

/-! ## L893 `3e97a39311f3`: So $uLu^{-1}\le L$, and \eqref{eq:intertwine} gives the last
assertion. -/

#audit_axioms GroupApproximation.Manuscript.NonMFSentences.OneSidedSentences.manuscriptSentence_compressionCellCoreAndOffDiag
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.RankFourCompressionCellPrinted.compressor_conj_core_offDiag_sandwich
#audit_axioms GroupApproximation.OneSidedCompressor.compressor_compresses_core

/-! ## L893 `8782d1207725`: both sides differ from $u$ by one entry, $sa$ in position $(i,j)$,
since on the right the increment $sat\cdot(s,\ldots,et^{j-1})$ from row $j$ of $u$ … -/

#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingSentences.manuscriptSentence_intertwineEntries

/-! ## L899 `d1142160bf17`: The element -/

#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingSentences.manuscriptSentence_centralMark
#audit_axioms GroupApproximation.Manuscript.NonMF.RingCompressionCellGeneral.PrintedCentralMark
#audit_closed_axioms GroupApproximation.Manuscript.NonMF.RingCompressionCellGeneral.printedCentralMark

/-! ## L904 `0f4f9e94cc50`: Both $uc$ and $e_{12}(e)u$ equal $u+et\,E_{14}$: the last column of
$uc$ is $(e,et,et^2,t^3)^{\mathsf T}(1+et)$ and $e^2=e$, $te=0$, while … -/

#audit_axioms GroupApproximation.OneSidedCompressor.compressor_mul_centralMark

/-! ## L904 `419d553a0d48`: So $ucu^{-1}=e_{12}(e)$, and the Steinberg relation
$[e_{12}(e),e_{23}(1)]=e_{13}(e)$ gives the second identity. -/

#audit_axioms GroupApproximation.OneSidedCompressor.compressor_conj_centralMark
#audit_axioms GroupApproximation.OneSidedCompressor.defect_eq

/-! ## L904 `83ed5eb3b38c`: is computed in the block on coordinates $(1,4)$ using $te=0$, and a
diagonal matrix of this shape commutes with every $\operatorname{diag}(A,1)$, so … -/

#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingSentences.manuscriptSentence_centralMarkCentral
#audit_axioms GroupApproximation.Manuscript.NonMF.RingCompressionCellGeneral.PrintedCentralMarkCentral
#audit_closed_axioms GroupApproximation.Manuscript.NonMF.RingCompressionCellGeneral.printedCentralMarkCentral
#audit_axioms GroupApproximation.Manuscript.NonMF.RingCompressionCellGeneral.core_isBlockDiagOne
#audit_axioms GroupApproximation.Manuscript.NonMF.RingCompressionCellGeneral.centralMarkMatrix_commute_blockDiagOne

/-! ## L919 `29118a9b250c`, `5cbedadd4606`: Let $R$ be a countable unital associative ring. -/

#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingEJZUnconditional.manuscriptFullComplementaryIdempotentsRankTwoAllCharacteristics

/-! ## L924 `7ce8c636a470` (definition): that is, $1-st$ is a \emph{full} idempotent, so that
$1=\sum_{j}a_j(1-st)b_j$ for finitely many $a_j,b_j\in R$. -/

#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRankTwo.PrintedFullComplementaryIdempotentsRankTwo
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingEJZUnconditional.manuscriptFullComplementaryIdempotentsRankTwoAllCharacteristics

/-! ## L924 `cede6c4edd2c`: For every $n\ge2$, every homomorphism from $\EL_n(R)$ to an MF group
is trivial. Every homomorphism from $\EL_4(\mathcal C)$ to an MF group is … -/

#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingEJZUnconditional.manuscriptFullComplementaryIdempotentsRankTwoAllCharacteristics
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.UniversalGroupSigma.manuscriptFullComplementaryIdempotentsUniversal

/-! ## L936 `0939d33e1ff4`: The ring $\mathcal C$ is nonzero, since it maps onto $L_{\F_2}(1,2)$,
and finitely generated, so both groups have property~\textup{(T)} … -/

#audit_closed_axioms GroupApproximation.Manuscript.NonMFSentences.EJZCitationSentences.manuscriptSentence_universalRingBothGroupsPropertyT
#audit_closed_axioms GroupApproximation.Manuscript.NonMFSentences.UniversalRingSentences.manuscriptSentence_universalRingPrintedReasons
#audit_closed_axioms GroupApproximation.Manuscript.NonMFSentences.UniversalRingSentences.universalToLeavitt_surjective
#audit_closed_axioms GroupApproximation.Manuscript.NonMFSentences.HeadlineCitationSentences.manuscriptSentence_propertyTGivesFinitelyGenerated

/-! ## L936 `469f1e197e95`: \emph{The universal group.} In $\mathcal C$ put $s=s_0$, $t=t_0$, and
$e=1-st$. -/

#audit_axioms GroupApproximation.UniversalPair.pairInverse
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.UniversalGroupB.B

/-! ## L936 `a4cdcda5bef7`: Then $ts=1$, $e^2=e$, $es=te=0$, and $t_1es_1=1$. -/

#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingSentences.manuscriptSentence_ringRelations

/-! ## L936 `a6ce75cd2625`: Put $G=\EL_4(\mathcal C)$ and $L=\EL_3(\mathcal C)$ on coordinates
$1,2,3$. -/

#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingSentences.manuscriptSentence_groupsGandL

/-! ## L945 `ade7fe9335db`: By Lemma~\ref{lem:ring-compression-cell} there are $u,c\in G$ with
$uLu^{-1}\le L$, $c\in C_G(L)$, and -/

#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingSentences.manuscriptSentence_compressorMatrix
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingSentences.manuscriptSentence_centralMark

/-! ## L951 `8227dfc88059`: For arbitrary $a,b\in\mathcal C$, the Steinberg relations give -/

#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingSentences.manuscriptSentence_steinbergPair

/-! ## L951 `ec86ceff1bf1`: Let $N$ be the normal closure of $d$ in $G$. -/

#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingSentences.manuscriptSentence_normalClosureOfDefect

/-! ## L957 `8830867a92de`: For distinct $i,j,k$ and every $r\in\mathcal C$, -/

#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingSentences.manuscriptSentence_steinbergSpreadsCoefficients

/-! ## L957 `ad1cfff561d3`: Elementary signed permutation matrices conjugate this element to
every off-diagonal position, up to a sign, so $e_{ij}(1)\in N$ whenever $i\ne j$. -/

#audit_axioms GroupApproximation.ElementaryWeyl.elGen_one_mem_of_ne

/-! ## L957 `eb7d6fe7334e`: So $e_{42}(1)=e_{42}(t_1es_1)\in N$. -/

#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingSentences.manuscriptSentence_fullnessRootRewrite

/-! ## L964 `2e41521883fb`: By Theorem~\ref{thm:compression-criterion} with $K=G$, every
homomorphism from $G$ to an MF group is trivial. -/

#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingSentences.manuscriptSentence_homFromBTrivial

/-! ## L964 `c0333a70aec6`: So $N=G$, and $\mathfrak D_G(L)=G$. -/

#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingSentences.manuscriptSentence_defectIsEverything

/-! ## L968 `2d95c1b6384d`: Then $\varphi\colon s_i\mapsto v_i$, $t_i\mapsto w_i$ is a unital
ring homomorphism $\mathcal C\to R$, and it induces a homomorphism $\EL_4(\mathcal … -/

#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingSentences.manuscriptSentence_universalProperty

/-! ## L968 `45f5c651c852`: By Lemma~\ref{lem:two-copies} choose $v_0,v_1,w_0,w_1\in R$ with
$w_iv_j=\delta_{ij}$. -/

#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingSentences.manuscriptSentence_twoCopies

/-! ## L968 `546f936f3fbe`: Put -/

#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingSentences.manuscriptSentence_lengthTwoWords
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingSentences.manuscriptSentence_pIdem
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingSentences.manuscriptSentence_jMapDef

/-! ## L977 `45c0a7a24b09` (definition): For a $4\times4$ matrix $A$ over $R$ put -/

#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingSentences.manuscriptSentence_jMapDef

/-! ## L977 `53f2c41f65d9`: so that $T_iS_j=\delta_{ij}$, and put $p=\sum_iS_iT_i$. -/

#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingSentences.manuscriptSentence_lengthTwoWords
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingSentences.manuscriptSentence_pIdem

/-! ## L982 `605dfb0242a3`: Since $(1-p)S_i=0$ and $T_j(1-p)=0$, we have
$\jmath(AB)=\jmath(A)\jmath(B)$ and $\jmath(I)=1$, so
$\Psi(A)=\operatorname{diag}(\jmath(A),1)$ defines … -/

#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingSentences.manuscriptSentence_jMapMultiplicative
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingSentences.manuscriptSentence_psiIsDiag
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingSentences.manuscriptSentence_psiOnRoots

/-! ## L989 `16a8406515ce`: Composed with $\EL_4(\mathcal C)\to\EL_4(R)\to\EL_2(R)$ it is
trivial, so $\rho$ kills the image $\Psi(e_{12}(1))=\operatorname{diag}(1+S_1T_2,1)$ of … -/

#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingSentences.manuscriptSentence_imageOfB

/-! ## L989 `18ab8ca8e9ef`: by the computation in Lemma~\ref{lem:rank-two}, since $T_jS_i=0$. -/

#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingSentences.manuscriptSentence_psiOnRoots

/-! ## L989 `1a16fdba9df3`: So $\rho$ is trivial, and the image of $\EL_4(\mathcal C)$ in
$\EL_2(R)$ normally generates $\EL_2(R)$. -/

#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingSentences.manuscriptSentence_rhoTrivial
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingSentences.manuscriptSentence_generatorNormallyGeneratesEL2

/-! ## L989 `7fb55eb3f582`: Let $\rho$ be a homomorphism from $\EL_2(R)$ to an MF group. -/

#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingSentences.manuscriptSentence_imageOfB

/-! ## L989 `e440073f849c`: So $\Psi(\EL_4(R))\le\EL_2(R)$. -/

#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingSentences.manuscriptSentence_psiLandsInEL2

/-! ## L999 `8487a62c655f`: A homomorphism from $\EL_n(R)$ to an MF group is trivial on that
copy, hence trivial, and the image of $\EL_4(\mathcal C)$ in that copy normally … -/

#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingSentences.manuscriptSentence_homFromELnTrivial
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingSentences.manuscriptSentence_imageOfBNormallyGeneratesELn

/-! ## L999 `f6edc460fb1b`: \emph{All ranks.} For $n\ge3$, signed permutation matrices conjugate
$e_{12}(r)$ to $e_{ij}(\pm r)$ for all $i\ne j$, so the copy of $\EL_2(R)$ on … -/

#audit_closed_axioms GroupApproximation.Manuscript.NonMFSentences.FullDefectAllRanksSentences.manuscriptSentence_allRanksSignedPermutations
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.TorsionComplementaryIdempotents.elGen_mem_of_ne_signedPermutation

/-! ## L1008 `34366ed3b6a0`: The full-defect hypothesis itself need not pass to $R$, nor need
every homomorphism from $\EL_n(R)$ to an MF group be trivial. -/

#audit_closed_axioms GroupApproximation.Manuscript.NonMFSentences.FullDefectCornerRemark.manuscriptSentence_hypothesisNeedNotPass

/-! ## L1017 `017719ec2a80`: The same conclusion holds for $R=L_k(1,m)$, for every countable
field $k$ and every $m\ge2$. -/

#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingEJZUnconditional.manuscriptLeavittAlgebraFullDefectRankTwoAllCharacteristics

/-! ## L1017 `97fcf1f9add1`: If $R$ is a countable simple unital ring that is not directly
finite, then every homomorphism from $\EL_n(R)$ to an MF group is trivial for every … -/

#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingEJZUnconditional.manuscriptSimpleInfiniteRingRankTwoAllCharacteristics

/-! ## L1027 `4515e83a1b91`: In the first case choose $ts=1\ne st$; then $1-st$ is a nonzero
idempotent, and since $R$ is simple it generates $R$ as a two-sided ideal. In the … -/

#audit_axioms GroupApproximation.Manuscript.NonMFSentences.OneSidedCorollarySentences.manuscriptSentence_simpleCaseIdempotentFull
#audit_axioms GroupApproximation.Manuscript.NonMFSentences.OneSidedSentences.manuscriptSentence_simpleRingChooseAndFull
#audit_axioms GroupApproximation.Manuscript.NonMFSentences.OneSidedCorollarySentences.manuscriptSentence_leavittCaseSandwich
#audit_axioms GroupApproximation.Manuscript.NonMFSentences.OneSidedSentences.manuscriptSentence_leavittChooseAndFull

/-! ## L1035 `e490d00b41a0`: Theorem~\ref{thm:full-defect-ring} applies in both cases. -/

#audit_closed_axioms GroupApproximation.Manuscript.NonMFSentences.OneSidedSentences.manuscriptSentence_simpleInfiniteRingCorollaryStatement

/-! ## L1039 `18fd64bafd97` (definition): Let $R$ be a countable unital ring. -/

#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRing.PrintedOneSidedRingMaximalIsometry
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingEJZUnconditional.manuscriptOneSidedRingMaximalIsometryAllCharacteristics

/-! ## L1039 `7b383805ef7a`: If $R$ is not directly finite, then $C^*_{\max}(\EL_n(R))$ contains
a proper isometry for every $n\ge4$. -/

#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingEJZUnconditional.manuscriptOneSidedRingMaximalIsometryAllCharacteristics

/-! ## L1039 `fa3d9aa8ce2c`: If $R\ne0$ satisfies the hypothesis of Theorem~\ref{thm:full-defect-
ring}, then for every $n\ge2$ the algebra $C^*_{\mathrm r}(\EL_n(R))$ is … -/

#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingEJZUnconditional.manuscriptOneSidedRingMaximalIsometryRankTwoAllCharacteristics
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingEJZUnconditional.manuscriptOneSidedRingMaximalReducedCStarRankTwoAllCharacteristics
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingEJZUnconditional.manuscriptUnitGroupNotMFAllCharacteristics

/-! ## L1051 `27586e96ecfe`: Choose $s,t\in R$ with $ts=1\ne st$, and let $S$ be the unital
subring they generate. -/

#audit_axioms GroupApproximation.Manuscript.NonMFSentences.OneSidedSentences.manuscriptSentence_oneSidedMaximalChooseSubring

/-! ## L1051 `900689d5c4ac`: By Proposition~\ref{prop:max-infinite} applied to $L\le\EL_n(R)$ and
$u$, $C^*_{\max}(\EL_n(R))$ contains a proper isometry. -/

#audit_axioms GroupApproximation.Manuscript.NonMFSentences.OneSidedSentences.manuscriptSentence_oneSidedMaximalProperIsometry

/-! ## L1051 `b45891d88426`: Let $u$ and $L=\EL_3(S)$ be as in Lemma~\ref{lem:ring-compression-
cell} for $S$; then $L$ has property~\textup{(T)}~\cite[Theorem~1.1]{EJZ}, and the … -/

#audit_axioms GroupApproximation.Manuscript.NonMFSentences.OneSidedCorollarySentences.manuscriptSentence_strictCompressionWitness
#audit_axioms GroupApproximation.Manuscript.NonMFSentences.OneSidedSentences.manuscriptSentence_oneSidedMaximalStrictCompression
#audit_closed_axioms GroupApproximation.Manuscript.NonMFSentences.HeadlineCitationSentences.manuscriptSentence_pairSubringElementaryPropertyT

/-! ## L1060 `06d71da2d355`: So $R^\times$ is not MF\@. -/

#audit_closed_axioms GroupApproximation.Manuscript.NonMFSentences.OneSidedSentences.manuscriptSentence_oneSidedMaximalUnitGroupNotMF

/-! ## L1060 `2ff745dd7064`: If $R\ne0$ satisfies the hypothesis of Theorem~\ref{thm:full-defect-
ring}, then $G=\EL_n(R)$ is countable and nontrivial, and by … -/

#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRing.PrintedElementaryGroupNotMF
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingEJZUnconditional.manuscriptElementaryGroupNotMFAllCharacteristics

/-! ## L1060 `518cbfd6417d`: The algebra $C^*_{\mathrm r}(G)$ is separable, stably finite because
its canonical trace is faithful, and not MF by … -/

#audit_axioms GroupApproximation.reducedGroupCStar_separable_stablyFinite_not_isMFAlgebra

/-! ## L1060 `88cdb5eaabb4`: Finally, the map $\jmath$ from the proof of Theorem~\ref{thm:full-
defect-ring} is injective, since $T_i\jmath(A)S_j=A_{ij}$, and sends $\EL_4(R)$ … -/

#audit_axioms GroupApproximation.Manuscript.NonMFSentences.OneSidedSentences.manuscriptSentence_oneSidedMaximalJInjective
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRankTwo.isOperatorMF_of_injective

/-! ## L1073 `5970e738b4d9`: Let $R$ be a countable unital ring, let $s,t\in R$ satisfy $ts=1$,
and suppose that $e=1-st$ has finite additive order. -/

#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.TorsionComplementaryIdempotents.PrintedTorsionComplementaryIdempotents
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.TorsionComplementaryIdempotents.manuscriptTorsionComplementaryIdempotents

/-! ## L1073 `ed1dd8699cf4`: Then for every $n\ge4$, -/

#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.TorsionComplementaryIdempotents.manuscriptTorsionComplementaryIdempotents
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.TorsionComplementaryIdempotents.relativeElementary_le_mfHomKernel

/-! ## L1078 `7774b0de0638` (definition): where $\EL_n(R,ReR)$ is the normal closure of the
$e_{ij}(a)$ with $a\in ReR$. -/

#audit_axioms GroupApproximation.relativeElementary

/-! ## L1078 `ef7c374310ee`: In particular $\EL_n(R)$ is not MF when $e\ne0$, and if $R$ has
positive characteristic, then $\EL_4(R)$ MF implies that $R$ is directly finite. -/

#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.TorsionComplementaryIdempotents.manuscriptTorsionComplementaryIdempotents
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.TorsionComplementaryIdempotents.not_isCDEOperatorMF_of_pair
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.TorsionComplementaryIdempotents.manuscriptPositiveCharacteristicDirectFiniteness

/-! ## L1084 `057fe08fb3bb`: Let $S$ be the unital subring generated by $s,t$, and let
$L=\EL_3(S)$ occupy coordinates $1,2,3$ of $\EL_4(S)$; it has … -/

#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.TorsionComplementaryIdempotents.manuscriptSentence_pairSubringCoreKazhdan
#audit_closed_axioms GroupApproximation.Manuscript.NonMFSentences.HeadlineCitationSentences.manuscriptSentence_pairSubringElementaryPropertyT

/-! ## L1084 `1246801a6fc6` (definition): Put $f_{ij}=s^iet^j$. -/

#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.TorsionComplementaryIdempotents.fUnit
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.TorsionComplementaryIdempotents.manuscriptSentence_matrixUnits

/-! ## L1084 `1538c6bcbbec`: The criterion is applied to a subgroup $B\le\EL_4(S)$ with a central
element of finite order inside $\mathfrak D_B(L)$. -/

#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.TorsionComplementaryIdempotents.manuscriptSentence_centralFiniteOrderInDefect

/-! ## L1084 `647f63b250b2`: Since $es=te=0$, $f_{ij}f_{kl}=\delta_{jk}f_{il}$, so $f_{ij}^2=0$
for $i\ne j$. -/

#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.TorsionComplementaryIdempotents.manuscriptSentence_matrixUnits

/-! ## L1084 `6efe099d7fdb`: Write $D(a)=\operatorname{diag}(1,1,1,a)$; for $i\ne j$, $D(1\pm
f_{ij})=[e_{41}(f_{ii}),e_{14}(\pm f_{ij})]$ lies in $\EL_4(S)$. -/

#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.TorsionComplementaryIdempotents.lastDiag
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.TorsionComplementaryIdempotents.manuscriptSentence_diagonalCommutators

/-! ## L1084 `7eeed19cdc69` (definition): Put -/

#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.TorsionComplementaryIdempotents.manuscriptSentence_printedCell
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.TorsionComplementaryIdempotents.printedB

/-! ## L1084 `8113a9d8c968`: Let $u$ be the compressor of Lemma~\ref{lem:ring-compression-cell},
put $w_{ij}=(1+f_{ji})(1-f_{ij})(1+f_{ji})$, $r=w_{14}w_{25}$, and $v=uD(r)$. -/

#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.TorsionComplementaryIdempotents.manuscriptSentence_compressorWeylAndV

/-! ## L1084 `84ce319a4f15`: Since $D(r)$ centralizes $L$, $vLv^{-1}\le L$. -/

#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.TorsionComplementaryIdempotents.manuscriptSentence_vCompressesCore

/-! ## L1084 `cb0f08ae60a3`: If $e=0$, then $ReR=0$ and $\EL_n(R,ReR)=1$, so assume $e\ne0$. -/

#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.TorsionComplementaryIdempotents.manuscriptSentence_zeroIdempotentCase

/-! ## L1100 `5b7bdf2351a7`: If $me=0$ then $z^m=D(1+mf_{12})=1$, and $z\ne1$ because
$tf_{12}s^2=e\ne0$. -/

#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.TorsionComplementaryIdempotents.manuscriptSentence_zOrderAndNontrivial

/-! ## L1100 `7634d6cc067b`: Then -/

#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.TorsionComplementaryIdempotents.manuscriptSentence_twoCommutatorsKilled

/-! ## L1100 `9627d330af8b`: So $\langle z\rangle$ is a nontrivial finite central subgroup of $B$
inside $\mathfrak D_B(L)$, and Theorem~\ref{thm:compression-criterion} applied … -/

#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.TorsionComplementaryIdempotents.manuscriptSentence_criterionKillsCentralElement

/-! ## L1100 `aeeaaeadaad3`: So $d=[vcv^{-1},\ell]=e_{24}(-f_{02})$ lies in $\mathfrak D_B(L)$,
and $[y,d]=D(1-f_{12})=z^{-1}$ since $f_{02}f_{10}=0$ and $f_{10}f_{02}=f_{12}$; … -/

#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.TorsionComplementaryIdempotents.manuscriptSentence_defectElementAndZ

/-! ## L1100 `bc99235426ad`: The element $z$ commutes with $L$ and $v$, and with $c$ and $y$
because $f_{12}f_{02}=f_{02}f_{12}=f_{12}f_{10}=0$, so $\langle z\rangle$ is central … -/

#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.TorsionComplementaryIdempotents.manuscriptSentence_zCentral

/-! ## L1100 `ee85d796d83a`: Then $c\in C_B(L)$, and from $rf_{02}r^{-1}=f_{05}$,
$rf_{12}r^{-1}=f_{45}$, $f_{02}t^3=f_{05}$, and $t^3f_{45}=f_{12}t^3$, direct
multiplication … -/

#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.TorsionComplementaryIdempotents.manuscriptSentence_conjugationsByV

/-! ## L1116 `885d8e36762a`: If $R$ has characteristic $p>0$ then $pe=0$ for every such $e$, and
the contrapositive gives direct finiteness. -/

#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.TorsionComplementaryIdempotents.manuscriptSentence_positiveCharacteristic

/-! ## L1116 `bbf924af98ec`: For $e\ne0$, $e_{21}(e)\ne1$. -/

#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.TorsionComplementaryIdempotents.manuscriptSentence_rootNeOne

/-! ## L1116 `f40da910f45b`: are killed, hence every $e_{ij}(aeb)$ by the Steinberg relations and
signed permutations, hence $\EL_n(R,ReR)$. -/

#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.TorsionComplementaryIdempotents.manuscriptSentence_sandwichesAndRelativeElementaryKilled
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.TorsionComplementaryIdempotents.relativeElementary_span_le_of_elGen_mem

/-! ## L1122 `0a08ffd095d6`: For $J$ the inclusion of Proposition~\ref{prop:torsion-defect-ring}
is an equality. -/

#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.JacobsonSymbol.manuscriptSentence_jacobsonRadical

/-! ## L1122 `11137e57b26d`: The algebra $J$ acts faithfully on $V=\F_2^{(\mathbb N)}$ by the
shift, $e=1-st$ is the projection onto the first vector $b_0$ of the standard basis … -/

#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.JacobsonSymbol.manuscriptSentence_jacobsonShiftAction

/-! ## L1122 `754a868fc8f5`: So $\EL_n(J,JeJ)$ is this kernel; the quotient
$\EL_n(\F_2[z,z^{-1}])$ is residually finite, so MF, and -/

#audit_axioms GroupApproximation.JacobsonLaurent.manuscriptSentence_laurentElementaryResiduallyFiniteMF
#audit_axioms GroupApproximation.JacobsonLaurent.isOperatorMF_of_injective_into_binaryLaurentGL
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.JacobsonSymbol.manuscriptSentence_jacobsonKernelFinitary
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.JacobsonSymbol.manuscriptSentence_jacobsonRadical
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.JacobsonSymbol.radicalEquivSLUnion

/-! ## L1122 `76588fb18d3b`: Let $\GL_{\mathrm{fs}}(V^n)$ be the group of automorphisms $g$ of
$V^n$ such that $g-I$ has finite matrix support in this basis, a condition stronger … -/

#audit_axioms GroupApproximation.FinitaryLinear.binaryGLfs
#audit_axioms GroupApproximation.FinitaryLinear.mem_binaryGLfs_iff
#audit_axioms GroupApproximation.FinitaryLinear.manuscriptSentence_finiteSupportStrongerThanFiniteRank

/-! ## L1122 `7c69447e3d41`: Over $\F_2$ every element of $\GL_{\mathrm{fs}}(V^n)$ is a product
of transvections, and each transvection is a relative root $e_{ij}(f_{uv})$ or, … -/

#audit_axioms GroupApproximation.FinitaryLinear.manuscriptSentence_binaryGLfsProductOfTransvections
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.JacobsonSymbol.blockAct_elGen_matUnit
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.JacobsonSymbol.blockAct_commutator_matUnit

/-! ## L1122 `b47d06c5c362`: The Toeplitz--Jacobson algebra $J=\F_2\langle s,t\mid ts=1\rangle$
has $1-st\ne0$ of order two, while $J/J(1-st)J\cong\F_2[z,z^{-1}]\ne0$, so $1-st$ … -/

#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.JacobsonSymbol.manuscriptSentence_jacobsonQuotientLaurent

/-! ## L1122 `d5e56b196927`: The kernel of $\EL_n(J)\to\EL_n(\F_2[z,z^{-1}])$ lies in
$\GL_{\mathrm{fs}}(V^n)$. -/

#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.JacobsonSymbol.manuscriptSentence_jacobsonKernelFinitary

/-! ## L1145 `61b6abd03b91`: The rank four is three plus one. -/

#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.JacobsonRankFour.manuscriptSentence_fourthCoordinateMakesCompressionInvertible

/-! ## L1145 `6ba4fb85570c`: an infinite simple locally finite group. -/

#audit_closed_axioms GroupApproximation.FinitaryLinear.manuscriptSentence_binarySLUnionInfiniteSimpleLocallyFinite

/-! ## L1145 `a8ceb0650975`: A finite subgroup $L$ of a group $G$ admits no proper compression,
since $uLu^{-1}\le L$ forces $uLu^{-1}=L$; then $uC_G(L)u^{-1}=C_G(L)$ and … -/

#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.JacobsonRankTwo.manuscriptSentence_finiteSubgroupAdmitsNoProperCompression

/-! ## L1163 `2ff180315a15` (definition): Put $R=L_{\F_2}(1,2)$ and $H=R^\times$. -/

#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.RankFourEndpoint.R
#audit_axioms GroupApproximation.Manuscript.NonMFSentences.BinaryExampleSentences.BinaryExampleUnitGroup

/-! ## L1163 `98115b8e2580`: By~\eqref{eq:leavitt}, the maps $x\mapsto(t_0x,t_1x)$ and
$(y,z)\mapsto s_0y+s_1z$ are mutually inverse isomorphisms of right $R$-modules between
$R$ … -/

#audit_closed_axioms GroupApproximation.Manuscript.NonMFSentences.BinaryExampleSentences.manuscriptSentence_leavittModuleEquivProd
#audit_closed_axioms GroupApproximation.Manuscript.NonMFSentences.BinaryExampleSentences.manuscriptSentence_unitsEquivGLFourEqELFour

/-! ## L1163 `cbb223c4d600` (structural): We identify $H$ with $\EL_4(R)$. -/

#audit_closed_axioms GroupApproximation.Manuscript.NonMFSentences.BinaryExampleSentences.manuscriptSentence_weIdentifyHWithELFour

/-! ## L1170 `a71f65809e0b`: The relations give $t_0s_0=1$ and $t_1(1-s_0t_0)s_1=1$, so $R$
satisfies the hypothesis of Theorem~\ref{thm:full-defect-ring}, and every homomorphism … -/

#audit_closed_axioms GroupApproximation.Manuscript.NonMFSentences.HeadlineCitationSentences.manuscriptSentence_finitelyGeneratedGivesPropertyT
#audit_closed_axioms GroupApproximation.Manuscript.NonMFSentences.HeadlineCitationSentences.manuscriptSentence_propertyTGivesFinitelyGenerated
#audit_closed_axioms GroupApproximation.Manuscript.NonMFSentences.HeadlineCitationSentences.headlineGroup_finitelyGenerated_via_propertyT
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.RankFourEndpoint.hasKazhdanPropertyT_viaEJZ
#audit_closed_axioms GroupApproximation.Manuscript.NonMFSentences.BinaryExampleSentences.manuscriptSentence_relationsGiveTrivialHomomorphisms

/-! ## L1170 `e47b80780566`: Since $e_{12}(1)\ne1$, the group $H$ is nontrivial. -/

#audit_closed_axioms GroupApproximation.Manuscript.NonMFSentences.BinaryExampleSentences.manuscriptSentence_e12OneForcesNontrivial

/-! ## L1178 `2a57c4750c2a` (structural): Let $N$ be a normal subgroup of $H$. -/

#audit_closed_axioms GroupApproximation.Manuscript.NonMFSentences.BinaryExampleSentences.manuscriptSentence_letNBeNormalSubgroup

/-! ## L1178 `2bf4b5aca1b4`: The ring $R$ is purely infinite simple~\cite{AbramsAranda} and
therefore an exchange ring~\cite{AraExchange}, so by Preusser's sandwich … -/

#audit_closed_axioms GroupApproximation.manuscriptSentence_purelyInfiniteSimpleIsExchange
#audit_axioms GroupApproximation.PreusserSandwichExchange.binaryLeavitt_isPurelyInfiniteSimpleRing
#audit_axioms GroupApproximation.PreusserSandwichExchange.binaryLeavitt_isExchangeRing
#audit_closed_axioms GroupApproximation.PreusserSandwichExchange.manuscriptSentence_preusserSandwichForExchangeRings
#audit_closed_axioms GroupApproximation.PreusserSandwichExchange.manuscriptSentence_rankFourSandwich
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.sentence_53445fb2a2b7
#audit_axioms GroupApproximation.BinaryLeavitt.center_eq_bot
#audit_axioms GroupApproximation.BinaryLeavitt.hasRightExchange
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.sentence_9e719f10dc89
#audit_axioms GroupApproximation.Manuscript.NonMFSentences.BinaryExampleSentences.manuscriptSentence_purelyInfiniteExchangePreusserSandwich

/-! ## L1185 `7a20735318a1`: Since $R$ is simple, either $I=R$, and then $N\ge\EL_4(R)=H$, or
$I=0$, and then every $g\in N$ is central in $\GL_4(R)$. -/

#audit_axioms GroupApproximation.Manuscript.NonMFSentences.BinaryExampleSentences.manuscriptSentence_simpleGivesTrichotomy
#audit_axioms GroupApproximation.Manuscript.NonMFSentences.BinaryExampleSentences.manuscriptSentence_idealTopGivesNEqTop

/-! ## L1185 `8ed259b70c4a`: It is nontrivial, and every homomorphism from it to an MF group is
trivial, so $H$ is not MF\@. -/

#audit_closed_axioms GroupApproximation.Manuscript.NonMFSentences.BinaryExampleSentences.manuscriptSentence_HNontrivialAndNotMF

/-! ## L1185 `9085fad2968e`: In the second case, commuting with each $e_{ij}(1)$ forces
$g=\lambda I_4$ with $\lambda\in R^\times$, and commuting with each $e_{ij}(a)$ then gives
… -/

#audit_axioms GroupApproximation.Manuscript.NonMFSentences.BinaryExampleSentences.manuscriptSentence_fixGInN
#audit_axioms GroupApproximation.Manuscript.NonMFSentences.BinaryExampleSentences.manuscriptSentence_idealZeroGivesCentral
#audit_axioms GroupApproximation.Manuscript.NonMFSentences.BinaryExampleSentences.manuscriptSentence_commutingSingleForcesScalar
#audit_axioms GroupApproximation.Manuscript.NonMFSentences.BinaryExampleSentences.manuscriptSentence_commutingGeneralForcesCentral

/-! ## L1185 `bfd4d3ceba5a`: So $H$ is simple. -/

#audit_axioms GroupApproximation.Manuscript.NonMFSentences.BinaryExampleSentences.manuscriptSentence_thusNTrivial
#audit_closed_axioms GroupApproximation.Manuscript.NonMFSentences.BinaryExampleSentences.manuscriptSentence_HIsSimple
#audit_axioms GroupApproximation.PreusserAssembly.isSimpleGroup_elementaryGroup_binaryLeavitt_via_preusser
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.RankFourEndpoint.manuscriptPropositionSimple

/-! ## L1185 `d38df1795c78`: So $\lambda$ lies in $Z(R)=\F_2$~\cite[Corollary~4.3]{ArandaCrow},
and $N=1$. -/

#audit_axioms GroupApproximation.BinaryLeavitt.center_eq_bot
#audit_closed_axioms GroupApproximation.manuscriptSentence_leavittCentreIsBaseField
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.sentence_9e719f10dc89
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.sentence_4b5ccef4a04e
#audit_axioms GroupApproximation.Manuscript.NonMFSentences.BinaryExampleSentences.manuscriptSentence_centerEqF2GivesGEqOne

/-! ## L1185 `e4440282ed35` (definition): where $\EL_4(R,I)$ is the normal closure in $\EL_4(R)$
of the elementary matrices $e_{ij}(a)$ with $a\in I$, and $C_4(R,I)$ is the preimage of
the … -/

#audit_axioms GroupApproximation.relativeElementary
#audit_axioms GroupApproximation.congruenceSubgroup

/-! ## L1197 `ecb74cabf11a`: Since $R\ne0$ satisfies the hypothesis of Theorem~\ref{thm:full-
defect-ring}, Corollary~\ref{cor:one-sided-ring-maximal} shows that $C^*_{\mathrm … -/

#audit_closed_axioms GroupApproximation.Manuscript.NonMFSentences.BinaryExampleSentences.manuscriptSentence_reducedAndMaximalCStarClauses

/-! ## L1205 `1f5ca4f92217` (definition): Write $\kappa\colon R^\times\to K_1(R)$ for the
canonical map. -/

#audit_axioms GroupApproximation.AlgebraicK.kappa

/-! ## L1205 `4fb6ccd3e134`: The algebras $L_k(1,d)$ are purely infinite
simple~\cite{AbramsAranda}. -/

#audit_axioms GroupApproximation.AryLeavitt.isPurelyInfiniteSimpleRing

/-! ## L1205 `8fdc908a49c7` (definition): Let $\GL(R)$ and $\EL(R)$ be the direct limits of
$\GL_n(R)$ and $\EL_n(R)$ along $A\mapsto\operatorname{diag}(A,1)$; the subgroup $\EL(R)$
is normal … -/

#audit_axioms GroupApproximation.ClassicalGLColim
#audit_axioms GroupApproximation.elementaryColim
#audit_axioms GroupApproximation.StableWhitehead.elementaryColim_normal
#audit_axioms GroupApproximation.AlgebraicK.AlgebraicKOne

/-! ## L1205 `c0fe92a1903d` (definition): Two idempotents $e,f$ of a ring are \emph{equivalent}
if $e=xy$ and $f=yx$ for some $x,y$; an idempotent $e$ is \emph{infinite} if $e=f+g$ for … -/

#audit_axioms GroupApproximation.MFQuotientUnits.IsEquivalentIdempotent
#audit_axioms GroupApproximation.MFQuotientUnits.IsInfiniteIdempotent
#audit_axioms GroupApproximation.MFQuotientUnits.IsPurelyInfiniteSimpleRing

/-! ## L1219 `6b4a21de3f07`: Equivalently, $\Rad_{\mathrm{MF}}(\GL_n(R))=[\GL_n(R),\GL_n(R)]$ and
$\GL_n(R)/\Rad_{\mathrm{MF}}(\GL_n(R))\cong K_1(R)$. -/

#audit_closed_axioms GroupApproximation.MFQuotientUnitsKOne.manuscriptMFQuotientUnitsKOneAtBaseRing

/-! ## L1219 `c34115be7c92`: Then every homomorphism from $\GL_n(R)$ to an MF group factors
uniquely through the canonical map $\GL_n(R)\to K_1(R)$, and $K_1(R)$, a countable … -/

#audit_closed_axioms GroupApproximation.MFQuotientUnitsKOne.manuscriptCanonicalKOne
#audit_closed_axioms GroupApproximation.MFQuotientUnitsKOne.manuscriptMFQuotientUnitsKOne

/-! ## L1230 `23b488384d1b`: So $\kappa$ is a homomorphism to an MF group, and $N\le\ker\kappa$. -/

#audit_axioms GroupApproximation.MFQuotientUnitsSentences.manuscriptSentence_radicalLeKerKappa

/-! ## L1230 `55adb8bf7a88`: A countable abelian group $A$ is MF: $C^*_{\max}(A)$ is commutative
and separable, hence residually finite-dimensional and MF~\cite{BK}, and … -/

#audit_closed_axioms GroupApproximation.CountableAbelianMFPrintedRoute.manuscriptSentence_countableAbelianIsMFPrintedRoute
#audit_axioms GroupApproximation.CountableAbelianMFPrintedRoute.maximalGroupCStar_mul_comm
#audit_axioms GroupApproximation.CountableAbelianMFPrintedRoute.isResiduallyFiniteDimensional
#audit_axioms GroupApproximation.CountableAbelianMFPrintedRoute.isMFAlgebra
#audit_axioms GroupApproximation.CountableAbelianMFPrintedRoute.isOperatorMF

/-! ## L1230 `5c5eeda68a8a`: The ring $M_n(R)$ is again countable, purely infinite, and
simple~\cite[Corollary~1.7]{AGP}, and $K_1(M_n(R))\cong K_1(R)$ by Morita invariance, so … -/

#audit_axioms GroupApproximation.MFQuotientUnitsSentences.manuscriptSentence_matrixRingAgainPurelyInfinite
#audit_closed_axioms GroupApproximation.MFQuotientUnitsSteinberg.manuscriptSentence_reductionToRankOne
#audit_closed_axioms GroupApproximation.MFQuotientUnitsSteinberg.manuscriptSentence_sufficesRankOne

/-! ## L1230 `6c03d472e975`: Ara, Goodearl, and Pardo show that $\kappa$ is surjective with
kernel $[H,H]$~\cite[Theorem~2.4]{AGP}. -/

#audit_closed_axioms GroupApproximation.MFQuotientUnitsKOne.agpUnitKappa
#audit_closed_axioms GroupApproximation.MFQuotientUnitsKOne.agpUnitKappaResidue
#audit_axioms GroupApproximation.MFQuotientUnitsSentences.manuscriptSentence_kappaSurjectiveKernelCommutator
#audit_axioms GroupApproximation.MFQuotientUnitsSentences.manuscriptSentence_kappaSurjectiveKernelCommutatorAbstract

/-! ## L1230 `72f07338d806` (structural): Write $H=R^\times$ and $N=\Rad_{\mathrm{MF}}(H)$. -/

#audit_axioms GroupApproximation.MFQuotientUnits.mfHomKernel

/-! ## L1239 `ded89cfcd0e4` (structural): For the converse, a unit in $\ker\kappa$ is reduced
modulo $N$ to a unit of the form $e+(1-e)v(1-e)$, which is then the image of a stabilized
… -/

#audit_closed_axioms GroupApproximation.MFQuotientUnitsItemA.manuscriptSentence_itemA
#audit_closed_axioms GroupApproximation.MFQuotientUnitsStepOnePrinted.manuscriptSentence_stepOneParagraph

/-! ## L1239 `df9b558e0cb8`: Every nonzero idempotent $e$ of $R$ is
infinite~\cite[Proposition~1.5]{AGP}, so $eRe$ contains $s,t$ with $ts=e\ne st$, and $eRe$
is simple, so … -/

#audit_closed_axioms GroupApproximation.MFQuotientUnitsCornerUnits.manuscriptSentence_cornerRing

/-! ## L1239 `eefa8a852d05` (structural): We use Theorem~\ref{thm:full-defect-ring} in the
following form. -/

#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRankTwo.PrintedFullComplementaryIdempotentsRankTwo
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingEJZUnconditional.manuscriptFullComplementaryIdempotentsRankTwoAllCharacteristics

/-! ## L1252 `9fcd02a03747`: since these units form the image of $\EL_m(eRe)$ under a
homomorphism to $H$. -/

#audit_closed_axioms GroupApproximation.MFQuotientUnitsCornerUnits.manuscriptSentence_cornerUnits
#audit_axioms GroupApproximation.MFQuotientUnitsCornerUnits.cornerUnitsHom

/-! ## L1255 `afe1782dc7bc` (attribution): We use two facts from the proof
of~\cite[Theorem~2.4]{AGP}, which rest on~\cite[Proposition~1.5 and Corollary~1.7]{AGP}
and on the elementary … -/

#audit_closed_axioms GroupApproximation.MFQuotientUnitsKOne.manuscriptAGPInputs

/-! ## L1260 `49ff6f7e8ad6`: Then $R$ is the ring of $m\times m$ matrices over $T=e_1Re_1$, with
identity $\operatorname{diag}(1_T,\dots,1_T,f)$, whose last column has entries in … -/

#audit_closed_axioms GroupApproximation.MFQuotientUnitsItemA.manuscriptSentence_itemAMatrixRingAndFactorization
#audit_closed_axioms GroupApproximation.MFQuotientUnitsItemA.manuscriptSentence_itemA

/-! ## L1260 `64da88cf12a3`: [(a)] There are orthogonal idempotents $e_1,\dots,e_m$ with sum $1$,
$m\ge4$, such that $e_1,\dots,e_{m-1}$ are pairwise equivalent and $e_m$ is … -/

#audit_closed_axioms GroupApproximation.MFQuotientUnitsItemA.manuscriptSentence_itemADecomposition
#audit_closed_axioms GroupApproximation.MFQuotientUnits.printedItemA

/-! ## L1268 `1fd773c6c314`: [(b)] For a nonzero idempotent $e$ and $n\ge2$ there are an
idempotent $f<e$ equivalent to $e$ and orthogonal idempotents $r_2,\dots,r_n\le e-f$, … -/

#audit_closed_axioms GroupApproximation.MFQuotientUnitsItemB.manuscriptSentence_itemB
#audit_axioms GroupApproximation.MFQuotientUnitsItemB.matrixCornerEquiv

/-! ## L1277 `488237f2dec0`: Let $u\in\ker\kappa$ and write $u=gvh$ as in (a). -/

#audit_closed_axioms GroupApproximation.MFQuotientUnitsItemA.manuscriptSentence_itemAMatrixRingAndFactorization
#audit_closed_axioms GroupApproximation.MFQuotientUnits.printedItemAShape

/-! ## L1277 `8c6a65ba3286`: The elementary matrices with $i,j\le m-1$ form $\EL_{m-1}(T)$ inside
$(1-e_m)R(1-e_m)\cong M_{m-1}(T)$, so they lie in $N$ … -/

#audit_closed_axioms GroupApproximation.MFQuotientUnitsOffLastCorner.manuscriptSentence_offLastCorner
#audit_axioms GroupApproximation.MFQuotientUnitsOffLastCorner.cornerMatrixEquiv

/-! ## L1285 `2d6574150d4d`: are products of an element of $\EL_{m-1}(T)$ and a conjugate of its
inverse, so they lie in the normal subgroup $N$ as well. -/

#audit_closed_axioms GroupApproximation.MFQuotientUnitsSteinberg.manuscriptSentence_steinbergDisplaysInRadical
#audit_axioms GroupApproximation.MFQuotientUnitsSteinberg.lastColumnDisplay
#audit_axioms GroupApproximation.MFQuotientUnitsSteinberg.lastRowDisplay

/-! ## L1285 `f2f92d2bbb71`: Hence $u\equiv v$ modulo $N$, and $\kappa(v)=\kappa(u)=0$ because
$N\le\ker\kappa$. -/

#audit_closed_axioms GroupApproximation.MFQuotientUnitsCongruencePrinted.manuscriptSentence_congruenceModRadical

/-! ## L1290 `16df92a11bc9`: By the definition of $K_1$,
$\operatorname{diag}(v,1,\dots,1)\in\EL_n(R)$ for some $n\ge2$. -/

#audit_closed_axioms GroupApproximation.MFQuotientUnitsItemA.manuscriptDiagInElementary
#audit_axioms GroupApproximation.MFQuotientUnitsItemA.manuscriptSentence_diagInElementary
#audit_axioms GroupApproximation.MFQuotientUnitsItemA.manuscriptSentence_diagInElementaryAndCommutator

/-! ## L1290 `95141daa8321`: Hence $\ker\kappa\le N$. -/

#audit_axioms GroupApproximation.MFQuotientUnitsSentences.manuscriptSentence_conclusion
#audit_closed_axioms GroupApproximation.MFQuotientUnitsKOne.manuscriptMFQuotientUnitsKOne

/-! ## L1290 `c8680722d041`: With $\theta$ and $P$ as in (b),
$v=1-P+\theta(\operatorname{diag}(v,1,\dots,1))$, which lies in $N$ by~\eqref{eq:corner-
units}. -/

#audit_closed_axioms GroupApproximation.MFQuotientUnitsStepOnePrinted.manuscriptSentence_stepOneParagraph

/-! ## L1290 `ce26fc21c942` (structural): So let $v=e+(1-e)v(1-e)$ with $e\ne0$ and
$\kappa(v)=0$. -/

#audit_closed_axioms GroupApproximation.MFQuotientUnitsStepOnePrinted.manuscriptSentence_stepOneParagraph

/-! ## L1298 `6aef426dfc7a`: Then $H\cong\GL_d(R)$, and under this identification
$\Rad_{\mathrm{MF}}(H)=[H,H]=\EL_d(R)$ and -/

#audit_axioms GroupApproximation.LeavittKOneFormulaSentences.PrintedLeavittMFQuotientFull
#audit_closed_axioms GroupApproximation.LeavittKOneFormulaSentences.manuscriptLeavittMFQuotientFull
#audit_axioms GroupApproximation.LeavittKOneFormulaSentences.manuscriptSentence_quotientByElementaryIsScalarQuotient
#audit_closed_axioms GroupApproximation.LeavittKOneFormulaSentences.manuscriptLeavittKOneFormula

/-! ## L1307 `3c68c15758e8`: Theorem~\ref{thm:mf-quotient-units} identifies the radical with
$[H,H]$ and the quotient with $K_1(R)$. -/

#audit_axioms GroupApproximation.LeavittMFQuotientSentences.manuscriptSentence_theoremIdentifiesRadicalAndQuotient

/-! ## L1307 `4321530b3fec`: Khanh--Thanh show that $\GL_d(R)=\EL_d(R)D_d(k)$, where $D_d(k)$ is
the abelian group of diagonal matrices with entries in $k^\times$, which … -/

#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.KhanhThanhDiagonal.printedKhanhThanhDecomposition_everyArity
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.KhanhThanhDiagonal.scalarSurjective_everyArity
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.LeavittKOneFormula.scalarKernel
#audit_closed_axioms GroupApproximation.LeavittKOneFormulaSentences.manuscriptLeavittKOneFormula
#audit_axioms GroupApproximation.LeavittMFQuotientDiagonalSentence.PrintedKhanhThanhSentence
#audit_closed_axioms GroupApproximation.LeavittMFQuotientDiagonalSentence.manuscriptSentence_khanhThanhPrinted
#audit_axioms GroupApproximation.LeavittMFQuotientDiagonalSentence.mem_printedDiagonal_iff
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.KhanhThanhDiagonal.printedDiagonal

/-! ## L1307 `f6962254d259`: So $[H,H]\le\EL_d(R)$, while $\EL_d(R)\le[H,H]$ because every
homomorphism from $\EL_d(R)$ to an MF group is trivial … -/

#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.KhanhThanhDiagonal.manuscriptSentence_commutatorInElementaryPrinted
#audit_axioms GroupApproximation.LeavittMFQuotientBothInclusions.PrintedLeavittBothInclusions
#audit_closed_axioms GroupApproximation.LeavittMFQuotientBothInclusions.manuscriptSentence_bothInclusionsPrinted
#audit_axioms GroupApproximation.LeavittMFQuotientBothInclusions.elementary_le_commutator_of_trivial

/-! ## L1320 `6d3ca647302e`: For $d=2$ the quotient is trivial for every countable field $k$, so
every homomorphism from $L_k(1,2)^\times$ to an MF group is trivial. For … -/

#audit_axioms GroupApproximation.LeavittKOneQuotientEvaluations.PrintedLeavittQuotientTrivialRankTwo
#audit_closed_axioms GroupApproximation.LeavittKOneQuotientEvaluations.manuscriptSentence_quotientTrivialRankTwo
#audit_axioms GroupApproximation.LeavittKOneQuotientEvaluations.PrintedLeavittQuotientCyclicFiniteField
#audit_closed_axioms GroupApproximation.LeavittKOneQuotientEvaluations.manuscriptSentence_quotientCyclicFiniteField
#audit_closed_axioms GroupApproximation.LeavittScalarQuotient.manuscriptSentence_leavittScalarQuotientRankTwo
#audit_closed_axioms GroupApproximation.LeavittScalarQuotient.manuscriptSentence_leavittScalarQuotientFiniteField
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingEJZUnconditional.manuscriptLeavittMFQuotientTwoAllCharacteristics
