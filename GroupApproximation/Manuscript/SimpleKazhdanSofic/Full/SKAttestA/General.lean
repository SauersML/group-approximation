import GroupApproximation.Algebra.FinitaryLinearBinarySimple
import GroupApproximation.Dynamics.ClopenCrossedProduct
import GroupApproximation.Dynamics.SubshiftFiniteWindow
import GroupApproximation.Leavitt.CornerUnitHom
import GroupApproximation.Leavitt.ElementaryGroup
import GroupApproximation.Manuscript.SimpleKazhdanSofic.FiniteModelsAsymptotic
import GroupApproximation.Manuscript.SimpleKazhdanSofic.FiniteModelsForwardOrbit
import GroupApproximation.Manuscript.SimpleKazhdanSofic.FiniteModelsLeastPeriod
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.BrownROmega.Endpoints
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.BrownROmega.Factors
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.BrownROmega.GroupModel
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.BrownROmega.TensorModel
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.Definitions.SoficPrinted
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.Fibonacci.Endpoints
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.Fibonacci.Generation
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.Fibonacci.Model
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.Fibonacci.Words
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.GeneralExpanders.Expanders
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.GeneralExpanders.GeneralTheorem
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.GeneralExpanders.MarkedLimit
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.GeneralExpanders.Models
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.GeneralExpanders.WordEntries
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.GeneralRingT.Elementary
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.GeneralRingT.Endpoints
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.GeneralRingT.PartA
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.GeneralRingT.Ring
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.GeneralSimplicity.Endpoints
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.Halfline.HalflineA
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.Halfline.HalflineB
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.Halfline.LamplighterHost
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LEFCorollaries.GeneralSubgroupsRemark
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LEFCorollaries.PrintedHost
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LEFCorollaries.RecursiveHost
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LEFCorollaries.TuringDegree
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.MainTheorem.Endpoints
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.MainTheorem.ProofRest
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.MainTheorem.ProofSentences
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.Root.Corollaries
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.Root.Main
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.Root.Proof
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.Sharpness.Converse
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.Sharpness.Entries
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.Sharpness.Itinerary
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.Sharpness.Restriction
import GroupApproximation.Manuscript.SimpleKazhdanSofic.GeneralCommutatorProducts
import GroupApproximation.Manuscript.SimpleKazhdanSofic.GeneralCommutatorSpan
import GroupApproximation.Manuscript.SimpleKazhdanSofic.GeneralRingPropertyT
import GroupApproximation.Manuscript.SimpleKazhdanSofic.GeneralRoot
import GroupApproximation.Manuscript.SimpleKazhdanSofic.GeneralRootCoefficients
import GroupApproximation.Manuscript.SimpleKazhdanSofic.GeneralSimplicityNormalSubgroup
import GroupApproximation.Manuscript.SimpleKazhdanSofic.GeneralSimplicityStatement
import GroupApproximation.Manuscript.SimpleKazhdanSofic.GeneralTowerCopy
import GroupApproximation.Manuscript.SimpleKazhdanSofic.GeneralTowerUnits
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LamplighterAction
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LamplighterWP.Host
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LamplighterWP.Sentences
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LEFCharacterization
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LEFCharacterizationClosed
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LEFCorollaries.ExpanderLimitHosts
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LEFCorollaries.WordProblemHosts
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LEFHostInstances
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LEFHostInstancesClosed
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LEFHostInstancesLamplighterClosed
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LEFLevelEmbedding
import GroupApproximation.Manuscript.SimpleKazhdanSofic.MainAssembly
import GroupApproximation.Manuscript.SimpleKazhdanSofic.MainFromGeneral
import GroupApproximation.Manuscript.SimpleKazhdanSofic.MatricialMarkedLimit
import GroupApproximation.Manuscript.SimpleKazhdanSofic.MatricialMarkedLimitWords
import GroupApproximation.Manuscript.SimpleKazhdanSofic.MinimalSubshiftPeriodicWord
import GroupApproximation.Manuscript.SimpleKazhdanSofic.PeriodicMatrixUnits
import GroupApproximation.Manuscript.SimpleKazhdanSofic.RingPartitions
import GroupApproximation.Manuscript.SimpleKazhdanSofic.SubshiftMatricial
import GroupApproximation.Manuscript.SimpleKazhdanSofic.TowerCopyGroup
import GroupApproximation.Pestov91.SimpleModCentre
import GroupApproximation.Meta.AxiomGuard

/-!
# Attestation of thm:general and its proof (tex l.177–466)

Attestation of the `formalized` rows of `metadata/SK_SENTENCE_CENSUS.tsv` whose sentence starts at
`simple_kazhdan_sofic_group.tex` l.177–466 (census at manuscript commit 22cdba8c): 79 rows, 198 distinct
declarations.  Every declaration a row lists is audited here, grouped under its row, so that one build of
this module checks the axiom closure of the whole range at once.

* `#audit_closed_axioms` for theorems that take no input (the statement is a closed proposition);
* `#audit_axioms` for everything else: theorems whose inputs are the printed hypotheses of their sentence,
  definitions and structures.

Both fail the build on any axiom outside `propext`, `Classical.choice` and `Quot.sound`.  The signatures
were read by hand.  No declaration takes a `…Statement` or an owed proposition as input.  Proof-step
lemmas take the intermediate data of the printed proof (for example `GeneralCommutatorWitness`,
`IsCovariantPair`), and another declaration of the same row or proof supplies it.
A declaration listed by several rows is audited at its first row only.
-/

-- 4420496f1fee, tex l.177–178 (thm:general): [\textup{(a)}] For every $n\ge3$, the group $\EL_n(R)$ is an infinite, finitely gener...
#audit_closed_axioms GroupApproximation.Full.SK03.printedGeneralPartA
#audit_axioms GroupApproximation.Full.SK02.generalSimple_printed
#audit_axioms GroupApproximation.Full.SK03.generalInfiniteFGKazhdan
#audit_closed_axioms GroupApproximation.Full.SKRoot.thm_general

-- 10c6704796c1, tex l.184–187 (thm:general): Then for every $n\ge3$, $\EL_n(R)$, marked by the $e_{ij}(s)$ with $s\in S$, is an ex...
#audit_axioms GroupApproximation.Full.SK04.thm_general_b_printed
#audit_axioms GroupApproximation.Full.SK04.isMarkedLimit_matricial
#audit_axioms GroupApproximation.Full.SK04.isExpanderFamily_matricial
#audit_closed_axioms GroupApproximation.Full.SK04.printedGeneralTheorem
-- (1 further declaration(s) of this row are audited above)

-- 6f81d32bea17, tex l.191–192 (thm:general): Periodic approximations of $X$ give such maps, and Theorem~\ref{thm:main} follows.
#audit_closed_axioms GroupApproximation.Full.SK05.periodicApproximationsRemark
#audit_axioms GroupApproximation.Full.SK05.periodicMatricial_printed
-- (1 further declaration(s) of this row are audited above)

-- 9cfaf3b5009a, tex l.192–194 (thm:general): Lamplighter actions show that the countable subgroups of the groups in Theorem~\ref{t...
#audit_axioms GroupApproximation.Full.SK12.countableSubgroupsOfGeneral_iff
-- (1 further declaration(s) of this row are audited above)

-- e8b2abde6cb8, tex l.223–226: The ring $R=\bigoplus_{\xi\in\Lambda}\LC(C,\F_2)\,u_\xi$ has the multiplication $(fu_...
#audit_closed_axioms GroupApproximation.Full.SK03.printedGeneralRing

-- 173f18fa77ce, tex l.229–230: With $[g,h]=ghg^{-1}h^{-1}$ and $i,j,l$ distinct,
#audit_closed_axioms GroupApproximation.Full.SK03.printedGeneralElementaryIdentities
#audit_closed_axioms GroupApproximation.SimpleKazhdanSofic.printedGeneralElementaryIdentities

-- 321960985f46, tex l.231–233 (eq:elementary): [display] e_{ij}(r+r')=e_{ij}(r)e_{ij}(r'),\qquad [e_{il}(r),e_{lj}(r')]=e_{ij}(rr').
#audit_closed_axioms GroupApproximation.Full.SKRoot.eq_elementary
-- (1 further declaration(s) of this row are audited above)

-- 47723a292327, tex l.234–234: So the $e_{ij}(s)$ with $s\in S$ generate $G$.
#audit_axioms GroupApproximation.Full.SK03.elementaryGeneration
#audit_axioms GroupApproximation.Full.SK03.closure_elementaryGenerators_eq_top
#audit_axioms GroupApproximation.Full.SK03.elementaryGroup_fg
#audit_closed_axioms GroupApproximation.SimpleKazhdanSofic.printedGeneralElementaryGeneration
#audit_axioms GroupApproximation.SimpleKazhdanSofic.coefficientSubringFin

-- 1000b4dda3f2, tex l.234–237: By Ershov and Jaikin-Zapirain~\cite[Theorem~1.1]{EJZ}, $\EL_n$ of every finitely gene...
#audit_axioms GroupApproximation.Full.SK03.elementaryGroup_hasKazhdanPropertyT
#audit_closed_axioms GroupApproximation.Full.SK03.printedEJZ

-- 5c7e6bf6360f, tex l.237–238: It is infinite because $e_{12}(\LC(C,\F_2))$ is infinite.
#audit_axioms GroupApproximation.Full.SK03.infinite_elementaryGroup_of_injective
#audit_closed_axioms GroupApproximation.Full.SK03.printedE12Infinite

-- fcd5869cc6dc, tex l.241–241: Let $1\ne K\trianglelefteq G$ and $1\ne g\in K$.
#audit_axioms GroupApproximation.Full.SK02.stepThree_normalSubgroupEqTop
#audit_axioms GroupApproximation.Full.SK02.generalSimple

-- 1c33a0efb27c, tex l.241–242: We show in three steps that $K=G$.
-- (2 further declaration(s) of this row are audited above)

-- 9fde45f51872, tex l.245–246: Let $w\ge0$ bound the word lengths of the $\xi$ with $u_\xi$ occurring in the entries...
#audit_axioms GroupApproximation.Full.SK02.stepOne_smallSets

-- 89681b2636c0, tex l.249–251: Each $\xi\ne e$ fixes a closed set with empty interior, so the points moved by every ...
#audit_axioms GroupApproximation.Full.SK02.stepOne_movedPointsDense

-- 6b042d09b8a1, tex l.251–253: Small enough clopen neighborhoods of these points are small, so every nonempty clopen...
-- (1 further declaration(s) of this row are audited above)

-- 54ceec15a5e0, tex l.255–255: Some $h=e_{ij}(e_V)$ with $V$ small does not commute with $g$.
#audit_axioms GroupApproximation.Full.SK02.stepOne_nonCommutingRoot
#audit_axioms GroupApproximation.Full.SK02.stepOne_commutator
#audit_axioms GroupApproximation.SimpleKazhdanSofic.General.exists_isSmall_not_commute_elGen

-- 9c94086f2a8c, tex l.255–257: Indeed, $g$ commutes with $e_{ij}(r)$ exactly when $g_{pi}r=0$ for $p\ne i$, $rg_{jq}...
#audit_axioms GroupApproximation.SimpleKazhdanSofic.General.commute_elGen_iff
-- (1 further declaration(s) of this row are audited above)

-- f7fd3c8f31ea, tex l.257–259: For $c=\sum_\xi c_\xi u_\xi$ and small $V$ we have $ce_V=\sum_\xi c_\xi e_{\xi V}u_\x...
#audit_axioms GroupApproximation.SimpleKazhdanSofic.General.coeff_mul_charFn_apply
#audit_axioms GroupApproximation.SimpleKazhdanSofic.General.coeff_charFn_mul_apply
-- (1 further declaration(s) of this row are audited above)

-- f7414546517d, tex l.259–261: If $c_\xi\ne0$, it equals $1$ on a nonempty clopen set $U$, and a small set $V\subset...
#audit_axioms GroupApproximation.SimpleKazhdanSofic.General.exists_eq_one_of_ne_zero
#audit_axioms GroupApproximation.SimpleKazhdanSofic.General.exists_forall_coeff_mul_charFn_ne_zero
#audit_axioms GroupApproximation.SimpleKazhdanSofic.General.exists_forall_coeff_charFn_mul_ne_zero
-- (1 further declaration(s) of this row are audited above)

-- 128014aac9d0, tex l.261–262: So if $g$ commutes with every such $h$, then $g$ is diagonal.
#audit_axioms GroupApproximation.SimpleKazhdanSofic.General.offDiag_eq_zero
#audit_axioms GroupApproximation.SimpleKazhdanSofic.General.eq_zero_of_forall_mul_charFn
#audit_axioms GroupApproximation.SimpleKazhdanSofic.General.eq_zero_of_forall_charFn_mul
-- (1 further declaration(s) of this row are audited above)

-- d0c1d6b200d3, tex l.262–265: In $g_{ii}e_V=e_Vg_{jj}$ the coefficients at $u_\xi$ with $\xi\ne e$ are supported in...
#audit_axioms GroupApproximation.SimpleKazhdanSofic.General.coeff_diag_eq_zero
-- (1 further declaration(s) of this row are audited above)

-- c8e749a3c9f3, tex l.265–266: The coefficients at $u_e$ agree on every small $V$, so they agree everywhere.
-- (1 further declaration(s) of this row are audited above)

-- 02049aee6dd1, tex l.267–268: Therefore $g=cI_3$ with $c\in\LC(C,\F_2)$, and comparing coefficients at $u_e$ in $cc...
-- (1 further declaration(s) of this row are audited above)

-- 3692a1707c7c, tex l.268–269: Then $x=[g,h]$ lies in $K\setminus\{1\}$.
#audit_axioms GroupApproximation.Full.SK02.commutator_mem_ne_one
-- (1 further declaration(s) of this row are audited above)

-- 5ce2f653f637, tex l.273–276: Since $\epsilon_{ab}\epsilon_{a'b'}=e_{a(V\cap b^{-1}a'V)}\,u_{ab^{-1}a'b'^{-1}}$ and...
#audit_axioms GroupApproximation.Full.SK02.stepTwo_epsilon_mul_epsilon
#audit_axioms GroupApproximation.SimpleKazhdanSofic.General.epsilon_mul_epsilon
#audit_axioms GroupApproximation.SimpleKazhdanSofic.IsCovariantPair

-- 18ac299bc474, tex l.276–279: As $h\ne I_3$, $V$ is nonempty, so the $\epsilon_{ab}$ span a ring $A_V\cong M_{|B_w|...
#audit_axioms GroupApproximation.Full.SK02.stepTwo_epsilon_ne_zero
#audit_axioms GroupApproximation.Full.SK02.stepTwo_ringCopy
#audit_axioms GroupApproximation.SimpleKazhdanSofic.General.epsilon_ne_zero
#audit_axioms GroupApproximation.SimpleKazhdanSofic.General.epsilonHom
#audit_axioms GroupApproximation.SimpleKazhdanSofic.General.epsilonHom_single
#audit_axioms GroupApproximation.SimpleKazhdanSofic.General.epsilonHom_injective
#audit_axioms GroupApproximation.SimpleKazhdanSofic.General.blockFlatEquiv
#audit_axioms GroupApproximation.SimpleKazhdanSofic.General.copyGL
#audit_axioms GroupApproximation.SimpleKazhdanSofic.General.copyGL_injective

-- 16fd7b95d922, tex l.279–282: Its image $H_V$ lies in $G$, since the transvections $e_{pq}(\epsilon_{ab})$ with $p\...
#audit_axioms GroupApproximation.Full.SK02.stepTwo_towerCopy
#audit_axioms GroupApproximation.SimpleKazhdanSofic.General.copyGL_mem_elementaryGroup
#audit_axioms GroupApproximation.SimpleKazhdanSofic.General.copyGL_transvection
#audit_axioms GroupApproximation.FinitaryLinear.elementaryGroup_zmodTwo_eq_top
#audit_axioms GroupApproximation.elementaryUnit_commutator

-- 224922eb8e98, tex l.285–288: [display] fu_a\,e_V\,f'u_b=f\,e_{aV}\,(f'\circ a^{-1})\,u_{ab} \in\{0,\epsilon_{a,b^{...
#audit_axioms GroupApproximation.Full.SK02.stepTwo_mul_charFn_mul_mem
#audit_axioms GroupApproximation.SimpleKazhdanSofic.General.single_mul_charFn_mul_single_mem

-- a5ac663b1706, tex l.289–289: since $f\circ a$ and $f'$ are constant on $V$.
#audit_axioms GroupApproximation.Full.SK02.stepTwo_epsilonSpan_mul_mem
-- (2 further declaration(s) of this row are audited above)

-- 5b3ad392ecb5, tex l.289–292: The entries of $ghg^{-1}-I_3=g\,e_VE_{ij}\,g^{-1}$ are sums of such products, and $h^...
#audit_axioms GroupApproximation.SimpleKazhdanSofic.General.mul_charFn_mul_mem
#audit_axioms GroupApproximation.SimpleKazhdanSofic.General.epsilonSpan_mul_mem
#audit_axioms GroupApproximation.SimpleKazhdanSofic.General.generalCommutatorWitness
-- (2 further declaration(s) of this row are audited above)

-- 2b5ba855ed5c, tex l.292–294: Then $y=1_VI_3+(x-I_3)$ and $y'=1_VI_3+(x^{-1}-I_3)$ satisfy $yy'=y'y=1_VI_3$, so $x=...
#audit_axioms GroupApproximation.Full.SK02.stepTwo_commutatorWitness
#audit_axioms GroupApproximation.SimpleKazhdanSofic.General.exists_copyGL_eq
#audit_axioms GroupApproximation.SimpleKazhdanSofic.General.mem_range_epsilonHom_of_mem_epsilonSpan
#audit_axioms GroupApproximation.ChainRadical.exists_cornerUnitHom_eq
-- (1 further declaration(s) of this row are audited above)

-- ebd3562205bb, tex l.294–296: As $K\cap H_V$ is a nontrivial normal subgroup of $H_V\cong\GL_d(\F_2)=\PSL_d(\F_2)$,...
#audit_axioms GroupApproximation.Full.SK02.stepTwo_glSimple
#audit_axioms GroupApproximation.SimpleKazhdanSofic.General.eq_top_of_generalCommutatorWitness
#audit_axioms GroupApproximation.FinitaryLinear.isSimpleGroup_units_matrix_zmodTwo
#audit_axioms GroupApproximation.SimpleKazhdanSofic.det_units_matrix_zmodTwo
#audit_axioms GroupApproximation.SimpleKazhdanSofic.center_units_matrix_zmodTwo_eq_bot
#audit_axioms GroupApproximation.SimpleKazhdanSofic.General.epsilon_one_one
-- (1 further declaration(s) of this row are audited above)

-- fce7dd31894b, tex l.299–302: The set $J=\{r\in R:e_{pq}(r)\in K\text{ for all }p\ne q\}$ is a two-sided ideal by~\...
#audit_axioms GroupApproximation.Full.SK02.stepThree_levelIdeal

-- 8269b12fdd2c, tex l.302–303: It contains $e_V$, so it contains every $e_{\xi V}=u_\xi e_Vu_\xi^{-1}$.
#audit_axioms GroupApproximation.Full.SK02.stepThree_charFn_smul_mem
#audit_axioms GroupApproximation.SimpleKazhdanSofic.General.unit_mul_charFn_mul_inv
#audit_axioms GroupApproximation.SimpleKazhdanSofic.General.one_mem_levelIdeal_of_smul_cover
#audit_axioms GroupApproximation.Pestov91.SimpleModCentre.levelIdeal
#audit_axioms GroupApproximation.Pestov91.SimpleModCentre.mem_levelIdeal

-- 0ff037d08f90, tex l.303–305: By minimality and compactness finitely many of these sets cover $C$, so $1=1-\prod_i(...
#audit_axioms GroupApproximation.Full.SK02.stepThree_finiteCover
#audit_axioms GroupApproximation.Full.SK02.stepThree_one_mem

-- 91be68c586d4, tex l.305–305: Then $J=R$ and $K=G$.
#audit_axioms GroupApproximation.Full.SK02.stepThree_eq_top_of_one_mem

-- fffbd3d9a534, tex l.305–305: This proves~(a).
-- (2 further declaration(s) of this row are audited above)

-- 98c0dc44dff3, tex l.321–322: Both are onto, so $G$ and $\EL_3(M_{N_k}(\F_2))$ are quotients of $\EL_3(\mathcal A)$.
#audit_axioms GroupApproximation.Full.SK04.lift_surjective_of_closure

-- aae3dce58326, tex l.322–325: Here $\EL_3(M_{N_k}(\F_2))=\SL_{3N_k}(\F_2)$, as transvections generate $\SL_{3N_k}(\...
#audit_axioms GroupApproximation.Full.SK04.coe_elementaryBlockEquivSL_apply
#audit_axioms GroupApproximation.Full.SK04.isSimpleGroup_sl

-- fe0b43aae359, tex l.325–327: The group $\EL_3(\mathcal A)$ is generated by the $e_{ij}(1)$ and $e_{ij}(\tau_s)$, a...
#audit_axioms GroupApproximation.Full.SK04.closure_range_elementaryLetterMarking
#audit_axioms GroupApproximation.Full.SK04.isMarkedLimit_slMarking

-- dc18fb5cd4e3, tex l.327–331: A word of length $\lambda$ or less in the $e_{ij}(\tau_s)$ has entries of degree at m...
#audit_axioms GroupApproximation.Full.SK04.eventually_lift_eq_one

-- a339b883c9d3, tex l.331–332: So a word that is trivial in $G$ is trivial in $\SL_{3N_k}(\F_2)$ for large $k$.
#audit_axioms GroupApproximation.Full.SK04.eventually_entries_lift
#audit_axioms GroupApproximation.SimpleKazhdanSofic.eventually_mapMatrix_eq_one
#audit_axioms GroupApproximation.SimpleKazhdanSofic.isMarkedLimit_of_matricial
-- (1 further declaration(s) of this row are audited above)

-- 7c94ad64771a, tex l.333–334: As $G$ is simple, $e_{12}(1)$ is a product of conjugates of $w$ and $w^{-1}$ in $G$.
#audit_axioms GroupApproximation.Full.SK04.eventually_lift_ne_one

-- 0b0cbb3733fe, tex l.334–336: This relation holds in $\SL_{3N_k}(\F_2)$ for large $k$, where $e_{12}(1)$ maps to th...
-- (2 further declaration(s) of this row are audited above)

-- 10c9c86a2224, tex l.336–338: Therefore these marked finite simple groups converge to $G$, so $G$ is LEF, and $N_k\...
#audit_axioms GroupApproximation.Full.SK04.tendsto_card_of_isMarkedLimit
-- (1 further declaration(s) of this row are audited above)

-- 8624ac81bcce, tex l.338–342: Since $\EL_3(\mathcal A)$ has property~\textup{(T)}~\cite[Theorem~1.1]{EJZ}, the Cayl...
#audit_axioms GroupApproximation.Full.SK04.isExpanderFamily_of_hasKazhdanPropertyT_images
#audit_axioms GroupApproximation.Full.SK04.isExpanderFamily_slMarking

-- 97c23b19a1af, tex l.345–348: It is LEF, so it is sofic~\cite[Example~4.5]{Pestov} and hyperlinear~\cite[Theorem~2]...
#audit_axioms GroupApproximation.Full.SK06.brownFormulation_general
#audit_axioms GroupApproximation.Full.SK06.exists_groupVonNeumann_embedding
#audit_axioms GroupApproximation.Full.SK01.printedIsSofic_iff
#audit_axioms GroupApproximation.Full.SK01.printedIsHyperlinear_of_isSofic

-- f43470fad63f, tex l.349–350: As $G$ is infinite and simple, its nontrivial conjugacy classes are infinite, so $L(G...
#audit_axioms GroupApproximation.Full.SK06.isBrownROmegaForm
#audit_closed_axioms GroupApproximation.Full.SK06.printedBrownFactors
-- (1 further declaration(s) of this row are audited above)

-- 5b15f5d8faae, tex l.350–355: Then $G$ lies in the unitary group of the McDuff factor $L(G)\mathbin{\bar\otimes}\ma...
#audit_axioms GroupApproximation.Full.SK06.IsBrownROmegaForm
#audit_axioms GroupApproximation.Full.SK06.exists_tensorHyperfinite_embedding
-- (2 further declaration(s) of this row are audited above)

-- 879174153d4e, tex l.359–360 (sec:main): Let $\Z$ act on $X$ by powers of $T$, where $(Tx)_t=x_{t+1}$, and write $u=u_1$, so $...
#audit_axioms GroupApproximation.Full.SK05.covariance
#audit_axioms GroupApproximation.ClopenCrossedProduct.unit_mul_coeff_mul_inv
#audit_axioms GroupApproximation.SimpleKazhdanSofic.shiftMulAction
#audit_axioms GroupApproximation.SimpleKazhdanSofic.shift_smul_apply
#audit_axioms GroupApproximation.SimpleKazhdanSofic.ringEquiv

-- 4d2e3277d31f, tex l.360–362 (sec:main): Minimality and infiniteness imply that $X$ has no isolated points and $T$ has no peri...
#audit_axioms GroupApproximation.Full.SK05.perfectSpace_subshift
#audit_axioms GroupApproximation.Full.SK05.subshiftHomeo_zpow_apply_ne_self
#audit_axioms GroupApproximation.Full.SK05.isCantorSpace_subshift
#audit_axioms GroupApproximation.SimpleKazhdanSofic.perfectSpace_carrier
#audit_axioms GroupApproximation.SimpleKazhdanSofic.zpow_apply_ne_self
#audit_axioms GroupApproximation.SimpleKazhdanSofic.isTopologicallyFree_shift
#audit_axioms GroupApproximation.SimpleKazhdanSofic.compactSpace_carrier
#audit_axioms GroupApproximation.SimpleKazhdanSofic.IsTopologicallyFreeAction
-- (1 further declaration(s) of this row are audited above)

-- 0fd8cf7d1eed, tex l.362–367 (sec:main): The ring $R=\LC(X,\F_2)\rtimes_T\Z$ is generated by $S=\{1,u,u^{-1}\}\cup\{e_a:a\in A...
#audit_axioms GroupApproximation.Full.SK05.subring_closure_printedGenerators_eq_top
#audit_axioms GroupApproximation.Full.SK05.unit_zpow_mul_letterIndicator_mul_inv
#audit_axioms GroupApproximation.Full.SK05.prod_coordIndicator_apply

-- 2ffe206d32dd, tex l.369–371 (sec:main): By minimality the forward orbit of $x$ is dense, so every word of $X$ occurs in $x_{[...
#audit_axioms GroupApproximation.Full.SK05.forwardOrbit_dense
#audit_axioms GroupApproximation.Full.SK05.exists_recurrence_segment
#audit_axioms GroupApproximation.SimpleKazhdanSofic.subset_closure_forwardOrbit_of_minimal
#audit_axioms GroupApproximation.SimpleKazhdanSofic.exists_nat_word_eq_of_minimal

-- 63b955601626, tex l.371–373 (sec:main): So there is $m$ with $x_{[m-\ell,m+\ell]}=x_{[-\ell,\ell]}$ such that every word of l...
-- (1 further declaration(s) of this row are audited above)

-- e0aae9c0b4eb, tex l.373–374 (sec:main): The $m$-periodic sequence $y_\ell$ that agrees with $x$ on $[0,m)$ then agrees with $...
#audit_axioms GroupApproximation.Full.SK05.exists_periodic_sameWords_carrier
#audit_axioms GroupApproximation.SimpleKazhdanSofic.periodicExt

-- 72e70d46a29f, tex l.375–377 (sec:main): Every window of length $2\ell+1$ of $y_\ell$ is a translate of one centered in $[0,m)...
-- (1 further declaration(s) of this row are audited above)

-- a62656a98556, tex l.378–381 (sec:main): For $f$ depending only on coordinates in $[-\ell,\ell]$ let $D_\ell(f)\delta_t=f(T^ty...
#audit_axioms GroupApproximation.Full.SK05.rest_diagonal_mulVec_single
#audit_axioms GroupApproximation.Full.SK05.rest_cutoffModel_eq_sum
#audit_axioms GroupApproximation.SimpleKazhdanSofic.exists_asymptoticModels
#audit_axioms GroupApproximation.SimpleKazhdanSofic.AsymptoticModels
#audit_axioms GroupApproximation.WordGraph.exists_radius

-- eaea133373a7, tex l.383–388 (sec:main): Since $PD_\ell(f)P^{-1}=D_\ell(f\circ T^{-1})$ whenever $f$ depends only on coordinat...
#audit_axioms GroupApproximation.Full.SK05.rest_conj_diagonal
#audit_axioms GroupApproximation.Full.SK05.rest_models

-- 769f446cc3f5, tex l.388–390 (sec:main): The shifts $T^ty_\ell$, $0\le t<N_\ell$, are distinct, so products of the $P^iD_\ell(...
#audit_axioms GroupApproximation.Full.SK05.rest_matrixUnits
#audit_axioms GroupApproximation.SimpleKazhdanSofic.translates_distinct_of_leastPeriod
#audit_axioms GroupApproximation.SimpleKazhdanSofic.single_self_mem_closure
#audit_axioms GroupApproximation.SimpleKazhdanSofic.single_mem_closure
#audit_axioms GroupApproximation.SimpleKazhdanSofic.shiftMatrix_mul_diagonal_mul_shiftMatrix_neg

-- 150f8a07cf1f, tex l.390–391 (sec:main): Therefore $\varphi_\ell(S)$ generates $M_{N_\ell}(\F_2)$, and Theorem~\ref{thm:genera...
#audit_axioms GroupApproximation.Full.SK05.rest_theoremGeneralApplies
#audit_axioms GroupApproximation.Full.SK05.printedMainProofRest

-- 0f50f8a77012, tex l.394–396: For a homeomorphism $T$ of a Cantor set $X$, the group $\EL_3(\LC(X,\F_2)\rtimes_T\Z)...
#audit_axioms GroupApproximation.Full.SK07.simpleKazhdanIffMinimalSubshift

-- 4f364612bc6c, tex l.396–397: One direction is Theorem~\ref{thm:main}.
#audit_axioms GroupApproximation.Full.SK07.simpleKazhdan_of_conj_minimalSubshift

-- 97d4813d2d34, tex l.397–400: Conversely, a Kazhdan group is finitely generated~\cite[Theorem~1.3.1]{BHV}, and the ...
#audit_axioms GroupApproximation.Full.SK07.kazhdanEntriesGenerateRing_sentence
#audit_axioms GroupApproximation.Full.SK07.subring_closure_entries_eq_top

-- 0475e15cae3f, tex l.400–402: So the ring is generated by finitely many $\sum_jf_ju^j$, the translates of these $f_...
#audit_axioms GroupApproximation.Full.SK07.itineraryConjugacy_sentence
#audit_axioms GroupApproximation.Full.SK07.exists_subshift_conj_of_fg
#audit_axioms GroupApproximation.Full.SK07.isMinimal_of_conj

-- 21987895ad32, tex l.402–406: If a nonempty proper closed set $Y$ is invariant, restriction maps the group onto $\E...
#audit_axioms GroupApproximation.Full.SK07.restrictionNotSimple_sentence
#audit_axioms GroupApproximation.Full.SK07.restrict_surjective
#audit_axioms GroupApproximation.Full.SK07.not_isSimpleGroup_of_invariant

-- 6a7d80148886, tex l.410–411: Its words of length~$3$ are $001$, $010$, $100$ and $101$.
#audit_closed_axioms GroupApproximation.Full.SK08.fibonacciWordsLengthThree

-- 6ba1d861e3e3, tex l.411–412: These are also the words of length~$3$ of the $5$-periodic sequence $y$ with $y_{[0,5...
#audit_axioms GroupApproximation.Full.SK08.fibonacciPeriodicWords
#audit_axioms GroupApproximation.Full.SK08.five_le_of_periodic_words
#audit_axioms GroupApproximation.Full.SK08.fibonacciY

-- c7a82dda7b3a, tex l.413–414: With $\ell=1$ and $y$ in place of $y_\ell$ we get $N=5$ and the model of Figure~\ref{...
#audit_axioms GroupApproximation.Full.SK08.fibonacciModelSetup
#audit_closed_axioms GroupApproximation.Full.SK08.fibonacciModel_letter_false

-- 2bbbe17ed1de, tex l.415–432: [display] \varphi(u)=P= \begin{pmatrix} \cdot&\cdot&\cdot&\cdot&1\\ 1&\cdot&\cdot&\cd...
#audit_axioms GroupApproximation.Full.SK08.fibonacciDisplay
#audit_axioms GroupApproximation.Full.SK08.displayedP
#audit_axioms GroupApproximation.Full.SK08.displayedD

-- 8791c07bc14f, tex l.434–435: The windows of $y$ centered at $1$ and at $4$ are both $010$, so every $D_1(f)$ has e...
#audit_axioms GroupApproximation.Full.SK08.fibonacciWindowsEqual

-- e1ab388c37b7, tex l.435–437: But $P^3D_1(e_1)P^{-3}$ is diagonal with entry $y_{t-3}$ at $t$, so $D_1(e_1)\,P^3D_1...
#audit_axioms GroupApproximation.Full.SK08.fibonacciConjugateE44

-- 585d3c88eb8a, tex l.437–438: Then $P^{t-4}E_{44}P^{4-t}=E_{tt}$ and $P^{t'-t}E_{tt}=E_{t't}$ give every matrix unit.
#audit_axioms GroupApproximation.Full.SK08.fibonacciMatrixUnits
#audit_closed_axioms GroupApproximation.Full.SK08.fibonacciModelGeneratesMatrixRing

-- 3c6fe3cf8fbe, tex l.438–440: So $\varphi(S)$ generates $M_5(\F_2)$, and the $e_{ij}(\varphi(s))$ with $s\in S$ gen...
#audit_closed_axioms GroupApproximation.Full.SK08.fibonacciGeneratesSL15
#audit_closed_axioms GroupApproximation.Full.SK08.fibonacciGeneratesMatrices
#audit_axioms GroupApproximation.Full.SK08.fibonacciSL15

-- 3597b9cfdaff, tex l.454–456 (cor:lef): A finitely generated group is LEF if and only if it is a subgroup of an infinite, fin...
#audit_axioms GroupApproximation.Full.SK12.corLef_lefIffSubgroupOfHost
#audit_closed_axioms GroupApproximation.Full.SKRoot.cor_lef
#audit_axioms GroupApproximation.SimpleKazhdanSofic.LEFCorollaries.manuscriptSentence_lefIffSubgroupOfExpanderLimitHost
#audit_axioms GroupApproximation.SimpleKazhdanSofic.LEFCorollaries.IsExpanderLimitHost
#audit_axioms GroupApproximation.SimpleKazhdanSofic.LEFCorollaries.IsNeighborExpanderFamily

-- 35ac998d56f1, tex l.456–458 (cor:lef): For every finitely generated LEF group $\Gamma$ there is such a group containing $\Ga...
#audit_axioms GroupApproximation.Full.SK12.corLef_hostWithSameTuringDegree
#audit_axioms GroupApproximation.Full.SK11.halflineA
#audit_axioms GroupApproximation.Full.SK11.halflineB
#audit_axioms GroupApproximation.SimpleKazhdanSofic.LamplighterWP.manuscriptSentence_lefHostWordProblemAbove
#audit_axioms GroupApproximation.SimpleKazhdanSofic.LEFCorollaries.manuscriptSentence_lefHostWordProblemAbove
-- (1 further declaration(s) of this row are audited above)

-- dc9c8bfa9ef7, tex l.458–460 (cor:lef): So $\Gamma$ has solvable word problem if and only if it is a subgroup of such a group...
#audit_axioms GroupApproximation.Full.SK12.corLef_solvableWordProblemIffSubgroupOfHost
#audit_axioms GroupApproximation.Full.SK12.corLef_lefSolvableWordProblemIffSubgroupOfHost
#audit_closed_axioms GroupApproximation.Full.SK11.lamplighterHostSolvableWP
#audit_axioms GroupApproximation.SimpleKazhdanSofic.LamplighterWP.manuscriptSentence_solvableWordProblem_of_subgroupOfSolvableHost
#audit_closed_axioms GroupApproximation.SimpleKazhdanSofic.LamplighterWP.hostProof
#audit_axioms GroupApproximation.SimpleKazhdanSofic.LEFCorollaries.manuscriptSentence_solvableWordProblem_of_subgroupOfSolvableHost
-- (1 further declaration(s) of this row are audited above)

-- cc439ae277d4, tex l.464–464 (cor:host): Every countable LEF group is a subgroup of such a group.
#audit_axioms GroupApproximation.Full.SK12.corHost_countableLEFSubgroupOfHost
#audit_closed_axioms GroupApproximation.Full.SKRoot.cor_host
#audit_axioms GroupApproximation.SimpleKazhdanSofic.PrintedCountableLEFHost
#audit_closed_axioms GroupApproximation.SimpleKazhdanSofic.printedCountableLEFHost
#audit_axioms GroupApproximation.SimpleKazhdanSofic.lefUltraproductEmbeddingStatement
#audit_closed_axioms GroupApproximation.SimpleKazhdanSofic.lefLamplighterStatement

-- f375789b732f, tex l.464–466 (cor:host): The members of a set of finitely generated groups embed in a single such group if and...
#audit_axioms GroupApproximation.Full.SK12.corHost_familyEmbedsIffLEFCountableClasses
#audit_axioms GroupApproximation.SimpleKazhdanSofic.LEFCorollaries.manuscriptSentence_familyEmbedsIffLEFCountableClasses
-- (1 further declaration(s) of this row are audited above)

-- 9b1a6e7489a1, tex l.466–469 (cor:host): So one such group contains every recursively presented finitely generated LEF group, ...
#audit_axioms GroupApproximation.Full.SK12.corHost_recursivelyPresentedInstances
#audit_axioms GroupApproximation.SimpleKazhdanSofic.PrintedRecursivelyPresentedLEFHost
#audit_closed_axioms GroupApproximation.SimpleKazhdanSofic.printedRecursivelyPresentedLEFHost
#audit_axioms GroupApproximation.SimpleKazhdanSofic.PrintedRecursivelyPresentedLEFHostInstances
#audit_closed_axioms GroupApproximation.SimpleKazhdanSofic.printedRecursivelyPresentedLEFHostInstances
#audit_closed_axioms GroupApproximation.SimpleKazhdanSofic.printedFinitelyPresentedRFInstance
#audit_closed_axioms GroupApproximation.SimpleKazhdanSofic.printedRecursiveLanguageInstance
-- (1 further declaration(s) of this row are audited above)

