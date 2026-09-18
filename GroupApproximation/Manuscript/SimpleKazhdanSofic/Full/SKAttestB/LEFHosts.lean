import GroupApproximation.GroupTheory.AlgebraicUltraproductLEF
import GroupApproximation.GroupTheory.LevelCommutatorWords
import GroupApproximation.GroupTheory.LevelCommutatorWordsLevels
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.Halfline.HalflineA
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.Halfline.HalflineB
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LamplighterHost.HostLemma
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LamplighterHost.Models
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LamplighterHost.Setting
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LEFCorollaries.PrintedHost
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LEFCorollaries.RecursiveHost
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LEFCorollaries.TuringDegree
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LemmaNN.Embedding
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LemmaNN.LemmaNN
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LemmaNN.LevelAction
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LemmaNN.LevelWords
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LemmaNN.Ultraproduct
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.Root.Corollaries
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Host.Assembly
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Host.Models
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Host.Setup
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LamplighterAction
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LamplighterHost
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LamplighterModelMatrices
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LamplighterModelSequence
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LamplighterWP.Sentences
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LEFCharacterizationClosed
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LEFCorollaries.WordProblemHosts
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LEFDiagonalCommutators
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LEFLevelEmbedding
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LEFRestrictedSum
import GroupApproximation.Manuscript.SimpleKazhdanSofic.WordProblemDegreeInvariant
import GroupApproximation.Meta.AxiomGuard

/-!
# Census attestation, sec:lef: cor:host, lem:nn and lem:host

Attestation of the `formalized` rows of `metadata/SK_SENTENCE_CENSUS.tsv` whose sentence starts at
`simple_kazhdan_sofic_group.tex` l.481–600 (census at manuscript commit 22cdba8c): 34 rows, 102 distinct
declarations.  Every declaration a row lists is audited here, grouped under its row, so that one build of
this module checks the axiom closure of the whole range at once.

* `#audit_closed_axioms` for theorems that take no input (the statement is a closed proposition);
* `#audit_axioms` for everything else: theorems whose inputs are the printed hypotheses of their sentence,
  definitions and structures.

Both fail the build on any axiom outside `propext`, `Classical.choice` and `Quot.sound`.  The signatures
were read by hand, and no declaration here takes a `…Statement` or another owed proposition as an input.
A declaration listed by several rows is audited at its first row only.
-/

-- 73a7e1f78cbb, tex l.486–487 (cor:host): Lemma~\ref{lem:halfline} keeps the Turing degree of the word problem in both steps.
#audit_axioms GroupApproximation.Full.SK11.halflineA
#audit_axioms GroupApproximation.Full.SK11.halflineB
#audit_axioms GroupApproximation.Full.SK12.corLef_hostWithSameTuringDegree
#audit_closed_axioms GroupApproximation.Full.SKRoot.cor_host
#audit_axioms GroupApproximation.SimpleKazhdanSofic.LamplighterWP.manuscriptSentence_halflineKeepsTuringDegree
#audit_axioms GroupApproximation.SimpleKazhdanSofic.LamplighterWP.manuscriptSentence_lefHostWordProblemAbove
#audit_axioms GroupApproximation.SimpleKazhdanSofic.LEFCorollaries.manuscriptSentence_lefHostWordProblemAbove
#audit_axioms GroupApproximation.SimpleKazhdanSofic.printedWordProblemReducesUnderEmbedding

-- 597b938ffe5c, tex l.490–491 (lem:nn): Every countable LEF group is a subgroup of $[\Delta,\Delta]$ for an infinite LEF grou...
#audit_axioms GroupApproximation.Full.SK09.LemmaNNStatement
#audit_closed_axioms GroupApproximation.Full.SK09.lemmaNN
#audit_closed_axioms GroupApproximation.Full.SKRoot.lem_nn

-- 72824238072d, tex l.495–497 (lem:nn): Let $\Gamma=\{\gamma_1,\gamma_2,\dots\}$ be a countable LEF group; replacing $\Gamma$...
#audit_axioms GroupApproximation.Full.SK09.isTextbookLEF_prod
-- (2 further declaration(s) of this row are audited above)

-- 8b9c8012260d, tex l.497–499 (lem:nn): There are finite groups $Q_k$ and maps $\mu_k\colon\Gamma\to Q_k$ that are injective ...
#audit_axioms GroupApproximation.Full.SK09.Models
#audit_axioms GroupApproximation.Full.SK09.models_nonempty
#audit_axioms GroupApproximation.Full.SK09.testSet
#audit_axioms GroupApproximation.SimpleKazhdanSofic.LEFLevelEmbedding.Models
#audit_axioms GroupApproximation.SimpleKazhdanSofic.LEFLevelEmbedding.models_nonempty
#audit_axioms GroupApproximation.SimpleKazhdanSofic.LEFLevelEmbedding.Models.μ_one
-- (1 further declaration(s) of this row are audited above)

-- b4a7b7c6fe7a, tex l.499–502 (lem:nn): On $Q_k\times\Z/m_k$, with $m_k=|Q_k|$, let $t_k$ add $1$ to the second coordinate, a...
#audit_axioms GroupApproximation.Full.SK09.tPerm
#audit_axioms GroupApproximation.Full.SK09.fPerm
#audit_axioms GroupApproximation.Full.SK09.pow_val_add_one
-- (1 further declaration(s) of this row are audited above)

-- d00f0309aff7, tex l.502–504 (lem:nn): Then $[f_{jk},t_k]$ multiplies the first coordinate by $\mu_k(\gamma_j)$, as in the e...
#audit_axioms GroupApproximation.Full.SK09.commutator_fPerm_tPerm
#audit_axioms GroupApproximation.SimpleKazhdanSofic.printedCommutatorMultipliesFirstCoordinate
#audit_axioms GroupApproximation.LevelCommutatorWords.commutator_fPerm_tPerm
-- (1 further declaration(s) of this row are audited above)

-- bfda87b78048, tex l.504–508 (lem:nn): On $Q_k\times\Z/m_k\times\Z/4^{k+1}$ let $b_k$ add $1$ to the last coordinate, and le...
#audit_axioms GroupApproximation.Full.SK09.aPerm
#audit_axioms GroupApproximation.Full.SK09.bPerm
#audit_axioms GroupApproximation.Full.SK09.levelAction
-- (1 further declaration(s) of this row are audited above)

-- e4fdf594781d, tex l.508–509 (lem:nn): Then $b_k^{-n}a_kb_k^n$ acts on the level $i$ as $a_k$ acts on the level $i+n$.
#audit_axioms GroupApproximation.Full.SK09.conjPow_aPerm_bPerm
#audit_axioms GroupApproximation.Full.SK09.shift_inv_mul_levelwise_mul_shift
#audit_axioms GroupApproximation.SimpleKazhdanSofic.printedConjugateMovesLevels
#audit_axioms GroupApproximation.LevelCommutatorWords.conjPow_aPerm_bPerm
-- (1 further declaration(s) of this row are audited above)

-- f5195da75a78, tex l.509–513 (lem:nn): As distinct ordered pairs of distinct powers of $2$ have distinct nonzero differences...
#audit_axioms GroupApproximation.Full.SK09.two_pow_sub_two_pow_inj
#audit_axioms GroupApproximation.Full.SK09.level_difference_zero
-- (1 further declaration(s) of this row are audited above)

-- 91ec6641e988, tex l.513–515 (lem:nn): So $w_j(a_k,b_k)$ acts by $[f_{jk},t_k]$ on the level $0$ and trivially on the other ...
#audit_axioms GroupApproximation.Full.SK09.word_aPerm_bPerm
#audit_axioms GroupApproximation.Full.SK09.word
-- (1 further declaration(s) of this row are audited above)

-- ef91849e35eb, tex l.515–519 (lem:nn): In the algebraic ultraproduct over $\omega$ of the symmetric groups of these sets, se...
#audit_axioms GroupApproximation.Full.SK09.embedding
#audit_axioms GroupApproximation.Full.SK09.embedding_injective
#audit_axioms GroupApproximation.Full.SK09.Ultraproduct
#audit_axioms GroupApproximation.SimpleKazhdanSofic.LEFLevelEmbedding.embedding
#audit_axioms GroupApproximation.SimpleKazhdanSofic.LEFLevelEmbedding.embedding_injective
#audit_axioms GroupApproximation.AlgebraicUltraproduct.Ultraproduct
-- (1 further declaration(s) of this row are audited above)

-- 2c6ae3ce7655, tex l.519–521 (lem:nn): It sends $\gamma_j$ to $w_j(a,b)$, where $a=(a_k)_k$ and $b=(b_k)_k$, so $\Gamma\le[\...
#audit_axioms GroupApproximation.Full.SK09.embedding_γ
#audit_axioms GroupApproximation.Full.SK09.embeddingΔ_mem_commutator
#audit_axioms GroupApproximation.Full.SK09.Delta
#audit_axioms GroupApproximation.SimpleKazhdanSofic.LEFLevelEmbedding.embedding_γ
#audit_axioms GroupApproximation.SimpleKazhdanSofic.LEFLevelEmbedding.Delta
#audit_axioms GroupApproximation.SimpleKazhdanSofic.LEFLevelEmbedding.embeddingΔ_mem_commutator
-- (1 further declaration(s) of this row are audited above)

-- 59fd8ce03585, tex l.522–524 (lem:nn): Finitely many equations and inequalities that hold in the ultraproduct hold in some c...
#audit_axioms GroupApproximation.Full.SK09.isLEF_delta
#audit_axioms GroupApproximation.Full.SK09.infinite_delta
-- (1 further declaration(s) of this row are audited above)

-- e20ebda53fb2, tex l.533–537 (lem:host): If $\Delta$ is infinite and LEF, then $G_\Delta$ is an infinite, finitely generated, ...
#audit_axioms GroupApproximation.Full.SK10.hostLemma
#audit_closed_axioms GroupApproximation.Full.SK10.printedHostLemma
#audit_closed_axioms GroupApproximation.Full.SKRoot.lem_host
#audit_axioms GroupApproximation.SimpleKazhdanSofic.Host.manuscriptSentence_hostLemma
#audit_axioms GroupApproximation.SimpleKazhdanSofic.Host.manuscriptSentence_commutatorContainment

-- 642a12a8acb2, tex l.541–542 (lem:host): The group $\Lambda$ is generated by $\Delta$ and the map $z$ adding $1$ at $e$, and i...
#audit_axioms GroupApproximation.Full.SK10.lamplighterMinimalTopologicallyFree
#audit_axioms GroupApproximation.SimpleKazhdanSofic.Host.manuscriptSentence_lambdaGenerationDenseOrbits
-- (1 further declaration(s) of this row are audited above)

-- ac91c158ed24, tex l.542–544 (lem:host): If $(\delta,c)\ne(e,0)$, the fixed points of $x\mapsto\delta x+c$ satisfy $x(\eta)=x(...
#audit_axioms GroupApproximation.SimpleKazhdanSofic.printedLamplighterMinimalTopologicallyFree
#audit_axioms GroupApproximation.SimpleKazhdanSofic.Lamplighter.smul_eq_self_iff
-- (2 further declaration(s) of this row are audited above)

-- a8760ee6d3af, tex l.544–547 (lem:host): In every cylinder over a finite set $W$ this fails at some point, for $\eta\in\operat...
#audit_axioms GroupApproximation.SimpleKazhdanSofic.Lamplighter.exists_moved_of_cylinder
-- (3 further declaration(s) of this row are audited above)

-- 2bcb951d302e, tex l.547–548 (lem:host): So the action is minimal and topologically free.
#audit_axioms GroupApproximation.SimpleKazhdanSofic.Lamplighter.isMinimal
#audit_axioms GroupApproximation.SimpleKazhdanSofic.Lamplighter.isTopologicallyFree
#audit_axioms GroupApproximation.SimpleKazhdanSofic.IsTopologicallyFreeAction
-- (3 further declaration(s) of this row are audited above)

-- 485cb4234583, tex l.548–550 (lem:host): The ring $R_\Delta$ is generated by $1$, the units $u_\xi^{\pm1}$ for $\xi$ in a fini...
#audit_axioms GroupApproximation.Full.SK10.lamplighterRingGeneration
#audit_axioms GroupApproximation.SimpleKazhdanSofic.Host.manuscriptSentence_ringGenerators
-- (1 further declaration(s) of this row are audited above)

-- bd0a4c539428, tex l.552–555 (lem:host): Let $\sigma_n\colon\Delta\to Q'_n$ be finite models of $\Delta$ that are injective on...
#audit_axioms GroupApproximation.Full.SK10.lamplighterBallModels
#audit_axioms GroupApproximation.SimpleKazhdanSofic.printedLamplighterBallModels
#audit_axioms GroupApproximation.SimpleKazhdanSofic.Lamplighter.IsBallModel
#audit_axioms GroupApproximation.SimpleKazhdanSofic.Lamplighter.exists_isBallModel
#audit_axioms GroupApproximation.SimpleKazhdanSofic.Lamplighter.BallModelSequence
-- (1 further declaration(s) of this row are audited above)

-- 1d5467454e25, tex l.559–563 (lem:host): For fixed $\xi,\xi'\in\Lambda$ and large $n$ we have $p_\xi p_{\xi'}=p_{\xi\xi'}$, an...
#audit_axioms GroupApproximation.Full.SK10.lamplighterModelActionAsymptotics
-- (1 further declaration(s) of this row are audited above)

-- cdb7675d1521, tex l.567–568 (lem:host): For fixed $f$ and $\xi$ and large $n$,
#audit_axioms GroupApproximation.Full.SK10.lamplighterModelMapAsymptoticHom
#audit_axioms GroupApproximation.SimpleKazhdanSofic.printedLamplighterModelMatrices
#audit_axioms GroupApproximation.SimpleKazhdanSofic.Lamplighter.eventually_modelPerm_mul_modelDiag_mul_inv
-- (1 further declaration(s) of this row are audited above)

-- ba51377f43f6, tex l.569–571 (lem:host): [display] P_\xi D_n(f)P_\xi^{-1}=D_n(f\circ\xi^{-1}),
#audit_axioms GroupApproximation.SimpleKazhdanSofic.Lamplighter.eventually_modelPerm_mul_modelDiag
-- (4 further declaration(s) of this row are audited above)

-- 52b4631053f0, tex l.572–573 (lem:host): so for fixed $r,r'\in R_\Delta$ and large $n$, $\varphi_n$ is additive and multiplica...
#audit_axioms GroupApproximation.SimpleKazhdanSofic.Host.manuscriptSentence_modelMapAsymptoticHom
-- (2 further declaration(s) of this row are audited above)

-- 96f0f64d19c7, tex l.573–577 (lem:host): The conjugates of $D_n(e_U)$ by products of the $P_\xi$ with $\xi$ in the generating ...
#audit_axioms GroupApproximation.Full.SK10.lamplighterModelGeneratorsGenerate
#audit_axioms GroupApproximation.SimpleKazhdanSofic.Host.manuscriptSentence_modelGeneratorsGenerate
-- (1 further declaration(s) of this row are audited above)

-- 0be755102247, tex l.577–578 (lem:host): Therefore Theorem~\ref{thm:general} applies to $R_\Delta$.
#audit_axioms GroupApproximation.Full.SK10.generalTheoremApplies
#audit_axioms GroupApproximation.SimpleKazhdanSofic.Host.manuscriptSentence_generalTheoremApplies
-- (1 further declaration(s) of this row are audited above)

-- 66cb283340f3, tex l.580–581 (lem:host): Finally, $\xi\mapsto\operatorname{diag}(u_\xi,1,1)$ is an injective homomorphism $\La...
#audit_axioms GroupApproximation.Full.SK10.lamplighterCommutatorContainment
#audit_axioms GroupApproximation.SimpleKazhdanSofic.printedLEFDiagonalEmbedding
#audit_axioms GroupApproximation.SimpleKazhdanSofic.lefDiagonalHom_injective
#audit_axioms GroupApproximation.SimpleKazhdanSofic.lefDiagonalHom_val
#audit_axioms GroupApproximation.SimpleKazhdanSofic.Lamplighter.unitHom_injective
-- (2 further declaration(s) of this row are audited above)

-- 69f426d03d8f, tex l.581–585 (lem:host): It maps $[\Lambda,\Lambda]$ into $G_\Delta$, since over $\F_2$ every unit $v$ satisfi...
#audit_axioms GroupApproximation.SimpleKazhdanSofic.printedLEFDiagonalIdentities
#audit_axioms GroupApproximation.SimpleKazhdanSofic.lefDiagonalHom_commutator_le
#audit_axioms GroupApproximation.SimpleKazhdanSofic.Lamplighter.exists_commutator_embedding
-- (4 further declaration(s) of this row are audited above)

-- b8360e2893c5, tex l.585–586 (lem:host): As $\Delta\le\Lambda$, the group $[\Lambda,\Lambda]$ contains $[\Delta,\Delta]$.
-- (4 further declaration(s) of this row are audited above)

-- a00a82b53387, tex l.589–592 (lem:host): [Proof of Corollary~\ref{cor:host} and of the first statement of Corollary~\ref{cor:l...
#audit_axioms GroupApproximation.Full.SK12.manuscriptSentence_limitsAndSubgroupsLEF
#audit_axioms GroupApproximation.Full.SK12.isTextbookLEF_of_isPrintedHost
#audit_axioms GroupApproximation.Full.SK12.isTextbookLEF_of_injective
#audit_axioms GroupApproximation.SimpleKazhdanSofic.Host.manuscriptSentence_markedLimitsLEF
-- (1 further declaration(s) of this row are audited above)

-- 6e7b67de6b16, tex l.592–594 (lem:host): Conversely, by Lemmas~\ref{lem:nn} and~\ref{lem:host} every countable LEF group is a ...
#audit_axioms GroupApproximation.Full.SK12.corHost_countableLEFSubgroupOfHost
#audit_axioms GroupApproximation.SimpleKazhdanSofic.Host.manuscriptSentence_countableLEFSubgroupOfHost
-- (3 further declaration(s) of this row are audited above)

-- e6ac216a5107, tex l.594–597 (lem:host): For the second statement of Corollary~\ref{cor:host}, apply the first to the restrict...
#audit_axioms GroupApproximation.Full.SK12.corHost_familyEmbedsIffLEFCountableClasses
#audit_axioms GroupApproximation.SimpleKazhdanSofic.restrictedSumLEFStatement
#audit_axioms GroupApproximation.SimpleKazhdanSofic.restrictedSum
#audit_axioms GroupApproximation.SimpleKazhdanSofic.countable_restrictedSum
#audit_axioms GroupApproximation.SimpleKazhdanSofic.isLEF_restrictedSum
#audit_closed_axioms GroupApproximation.SimpleKazhdanSofic.printedLEFFamilyHost
-- (1 further declaration(s) of this row are audited above)

-- 4d817ab1caf8, tex l.597–598 (lem:host): Conversely, a countable group has countably many finitely generated subgroups.
#audit_axioms GroupApproximation.SimpleKazhdanSofic.Host.manuscriptSentence_countableFGSubgroups
-- (2 further declaration(s) of this row are audited above)

-- 2d01550af9b2, tex l.598–600 (lem:host): The last statement of Corollary~\ref{cor:host} follows, as there are countably many r...
#audit_axioms GroupApproximation.Full.SK12.corHost_recursivelyPresentedInstances
#audit_axioms GroupApproximation.SimpleKazhdanSofic.Host.manuscriptSentence_recursivelyPresentedHost
-- (2 further declaration(s) of this row are audited above)

