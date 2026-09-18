import GroupApproximation.Computability.FiniteExtensionStep
import GroupApproximation.Computability.OracleTruthTable
import GroupApproximation.Computability.OracleUse
import GroupApproximation.Computability.PerfectTreeAntichain
import GroupApproximation.GroupTheory.LevelShiftDelta
import GroupApproximation.GroupTheory.LevelShiftDeltaWords
import GroupApproximation.Manuscript.SimpleKazhdanSofic.AbstractIntro.Questions
import GroupApproximation.Manuscript.SimpleKazhdanSofic.ContinuedFractionCutOracle
import GroupApproximation.Manuscript.SimpleKazhdanSofic.ContinuedFractionDigitOracle
import GroupApproximation.Manuscript.SimpleKazhdanSofic.ContinuedFractionExpansion
import GroupApproximation.Manuscript.SimpleKazhdanSofic.ContinuedFractionRepresentative
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.FinitelyPresented.Basic
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.FinitelyPresented.Endpoints
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.Halfline.HalflineA
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.Halfline.HalflineB
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.Halfline.LamplighterHost
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LEFCorollaries.TuringDegree
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.Root.Corollaries
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.WordProblems.Endpoints
import GroupApproximation.Manuscript.SimpleKazhdanSofic.HalflineA.Embedding
import GroupApproximation.Manuscript.SimpleKazhdanSofic.HalflineA.WordProblemReduction
import GroupApproximation.Manuscript.SimpleKazhdanSofic.HalflineB.Endpoints
import GroupApproximation.Manuscript.SimpleKazhdanSofic.HalflineB.Reduction
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LamplighterAffineWordProblemPrimrec
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LamplighterWP.Host
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LanguageReducesToWordProblem
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LEFCorollaries.WordProblemHosts
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LevelShiftDeltaWordProblem
import GroupApproximation.Manuscript.SimpleKazhdanSofic.QuestionsClosed
import GroupApproximation.Manuscript.SimpleKazhdanSofic.QuestionsNotFinitelyPresented
import GroupApproximation.Manuscript.SimpleKazhdanSofic.SturmianComputability
import GroupApproximation.Manuscript.SimpleKazhdanSofic.SturmianLanguage
import GroupApproximation.Manuscript.SimpleKazhdanSofic.SturmianSubshift
import GroupApproximation.Manuscript.SimpleKazhdanSofic.SturmianSubshiftMinimal
import GroupApproximation.Manuscript.SimpleKazhdanSofic.SturmianSubshiftSetting
import GroupApproximation.Manuscript.SimpleKazhdanSofic.TuringAntichain
import GroupApproximation.Manuscript.SimpleKazhdanSofic.WordProblemCriterion
import GroupApproximation.Manuscript.SimpleKazhdanSofic.WordProblemDegreeStatements
import GroupApproximation.Manuscript.SimpleKazhdanSofic.WordProblemReducesToLanguage
import GroupApproximation.Manuscript.SimpleKazhdanSofic.WordProblemReducesToLanguageInstance
import GroupApproximation.Meta.AxiomGuard

/-!
# Census attestation, lem:halfline, cor:wp and sec:questions

Attestation of the `formalized` rows of `metadata/SK_SENTENCE_CENSUS.tsv` whose sentence starts at
`simple_kazhdan_sofic_group.tex` l.601–800 (census at manuscript commit 22cdba8c): 32 rows, 104 distinct
declarations.  Every declaration a row lists is audited here, grouped under its row, so that one build of
this module checks the axiom closure of the whole range at once.

* `#audit_closed_axioms` for theorems that take no input (the statement is a closed proposition);
* `#audit_axioms` for everything else: theorems whose inputs are the printed hypotheses of their sentence,
  definitions and structures.

Both fail the build on any axiom outside `propext`, `Classical.choice` and `Quot.sound`.  The signatures
were read by hand, and no declaration here takes a `…Statement` or another owed proposition as an input.
A declaration listed by several rows is audited at its first row only.
-/

-- 210e288644f3, tex l.606–608 (lem:halfline): \textup{(a)} Every finitely generated LEF group $\Gamma$ is a subgroup of $[\Delta,\D...
#audit_axioms GroupApproximation.Full.SK11.halflineA
#audit_axioms GroupApproximation.Full.SK11.halflineA_solvable
#audit_closed_axioms GroupApproximation.Full.SKRoot.lem_halfline
#audit_axioms GroupApproximation.SimpleKazhdanSofic.HalflineA.manuscriptSentence_halflineEmbedding
#audit_axioms GroupApproximation.SimpleKazhdanSofic.HalflineA.turingReducible_wordProblemOracle_levelGen

-- fb18060da264, tex l.609–610 (lem:halfline): \textup{(b)} The word problem of $G_\Delta$ is Turing reducible to that of $\Delta$.
#audit_axioms GroupApproximation.Full.SK11.halflineB
#audit_axioms GroupApproximation.Full.SK11.halflineB_solvable
#audit_closed_axioms GroupApproximation.Full.SK11.lamplighterHostSolvableWP
#audit_axioms GroupApproximation.SimpleKazhdanSofic.Lamplighter.printedLamplighterAffineSolvableWordProblem
#audit_axioms GroupApproximation.SimpleKazhdanSofic.LamplighterWP.manuscriptSentence_halflineHostWordProblemReduction
#audit_closed_axioms GroupApproximation.SimpleKazhdanSofic.LamplighterWP.hostProof
-- (1 further declaration(s) of this row are audited above)

-- 6ca89f8e4ff1, tex l.619–622 (lem:halfline): Then $[\beta,h_\gamma]$ multiplies the level $0$ by $\gamma^{-1}$, so $\Delta=\langle...
#audit_axioms GroupApproximation.LevelShiftDelta.commutator_levelShift_levelMul
#audit_axioms GroupApproximation.LevelShiftDelta.levelDelta
#audit_axioms GroupApproximation.LevelShiftDelta.infinite_levelDelta
#audit_axioms GroupApproximation.LevelShiftDelta.exists_levelZeroEmbedding
-- (2 further declaration(s) of this row are audited above)

-- 81e60da3ab32, tex l.622–625 (lem:halfline): An element of $\Delta$ of length at most $\lambda$ is $f\beta^\ell$ with $|\ell|\le\l...
#audit_axioms GroupApproximation.SimpleKazhdanSofic.HalflineA.manuscriptSentence_halflineLevelNormalForm
-- (2 further declaration(s) of this row are audited above)

-- ef4082fc740e, tex l.625–630 (lem:halfline): Let $\psi$ map the ball of radius $2\lambda$ of $\Gamma$ injectively into a finite gr...
-- (2 further declaration(s) of this row are audited above)

-- 419672af4c27, tex l.630–635 (lem:halfline): The bijection $\kappa$ of $Q^{[-3\lambda,3\lambda]}$ given by $\kappa(x)_{-3\lambda}=...
-- (2 further declaration(s) of this row are audited above)

-- 5043611f4d0d, tex l.635–639 (lem:halfline): Let each $v\in Q^{[-3\lambda,3\lambda]}$ act on $Q^{[-3\lambda,3\lambda]}\times\Z/5\l...
-- (2 further declaration(s) of this row are audited above)

-- b4d347ea01a7, tex l.639–642 (lem:halfline): As $f$ is trivial below $-\lambda$ and constant from $\lambda$ on, $\zeta^\ell(\psi(f...
-- (2 further declaration(s) of this row are audited above)

-- 20cd8bd5a5e9, tex l.642–645 (lem:halfline): So $f\beta^\ell\mapsto(\psi(f(m)))_{|m|\le3\lambda}\,\zeta^\ell$ preserves the produc...
-- (2 further declaration(s) of this row are audited above)

-- 12a3a964a4e0, tex l.645–645 (lem:halfline): Therefore $\Delta$ is LEF.
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.HalflineB.manuscriptSentence_halflineDeltaIsLEF
-- (2 further declaration(s) of this row are audited above)

-- 86b1b005fc2a, tex l.647–650 (lem:halfline): From a word in the $\beta^{\pm1}$ and $h_\gamma^{\pm1}$ one computes the exponent sum...
#audit_axioms GroupApproximation.LevelShiftDelta.shiftPair
#audit_axioms GroupApproximation.LevelShiftDelta.hLetters
#audit_axioms GroupApproximation.LevelShiftDelta.valueWord
#audit_axioms GroupApproximation.LevelShiftDelta.isLevelForm_gValue
#audit_axioms GroupApproximation.SimpleKazhdanSofic.LevelShiftDeltaWordProblem.primrec_shiftPair
#audit_axioms GroupApproximation.SimpleKazhdanSofic.LevelShiftDeltaWordProblem.primrec_hLetters
#audit_axioms GroupApproximation.SimpleKazhdanSofic.LevelShiftDeltaWordProblem.primrec_valueWordAt
-- (3 further declaration(s) of this row are audited above)

-- 0b12bb409f63, tex l.650–652 (lem:halfline): It is trivial if and only if $\ell=0$ and these values are trivial in $\Gamma$, so th...
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.HalflineB.manuscriptSentence_halflineDeltaWordProblem
-- (3 further declaration(s) of this row are audited above)

-- 3c71f1b21217, tex l.654–657 (lem:halfline): For~(b), an element $x\mapsto\delta x+c$ of $\Lambda$ is given by a word for $\delta$...
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.HalflineB.manuscriptSentence_halflineLambdaWordProblem
-- (2 further declaration(s) of this row are audited above)

-- 7bfa078c0bed, tex l.657–661 (lem:halfline): A word in the generators of $G_\Delta$ multiplies out to a matrix with entries $\sum_...
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.HalflineB.manuscriptSentence_hostWordMultipliesOut
-- (2 further declaration(s) of this row are audited above)

-- e3cd35e16e2f, tex l.661–664 (lem:halfline): After collecting equal $\xi$ and equal coordinates, the word is trivial if and only i...
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.HalflineB.manuscriptSentence_hostTrivialityCriterion
-- (2 further declaration(s) of this row are audited above)

-- dfa561ecfaa5, tex l.665–665 (lem:halfline): So the word problem of $G_\Delta$ is Turing reducible to that of $\Delta$.
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.HalflineB.manuscriptSentence_hostWordProblemReduction
-- (3 further declaration(s) of this row are audited above)

-- 854c69bf6b59, tex l.669–672 (lem:halfline): By Lemmas~\ref{lem:halfline} and~\ref{lem:host}, $\Gamma$ is a subgroup of a group $G...
#audit_axioms GroupApproximation.Full.SK12.corLef_hostWithSameTuringDegree
-- (1 further declaration(s) of this row are audited above)

-- edd233afbf7b, tex l.672–675 (lem:halfline): Conversely, a word in the generators of $\Gamma$ becomes a word in the generators of ...
#audit_axioms GroupApproximation.Full.SK13.wp_reduces_under_embedding
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.HalflineB.manuscriptSentence_corLefSubstitution
-- (2 further declaration(s) of this row are audited above)

-- 2864647b9987, tex l.676–678 (lem:halfline): The last statement follows, as finitely generated subgroups of groups with solvable w...
#audit_axioms GroupApproximation.Full.SK12.corLef_solvableWordProblemIffSubgroupOfHost
#audit_axioms GroupApproximation.Full.SK12.corLef_lefSolvableWordProblemIffSubgroupOfHost
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.HalflineB.manuscriptSentence_corLefHeredity
-- (1 further declaration(s) of this row are audited above)

-- d8731f9b0b15, tex l.684–687 (cor:wp): The word problem of $G_X$ has the Turing degree of the language $L(X)$ of $X$, the se...
#audit_axioms GroupApproximation.Full.SK13.wp_degree_eq_language
#audit_axioms GroupApproximation.Full.SK13.wp_solvable_iff_recursive
#audit_closed_axioms GroupApproximation.Full.SK13.corollary
#audit_closed_axioms GroupApproximation.Full.SKRoot.cor_wp

-- 09c0f2ecb56e, tex l.687–689 (cor:wp): Every Turing degree is the degree of the word problem of some $G_X$, and there is a f...
#audit_axioms GroupApproximation.Full.SK13.every_degree
#audit_axioms GroupApproximation.Full.SK13.continuum_antichain
-- (2 further declaration(s) of this row are audited above)

-- 614923742ac7, tex l.693–696 (cor:wp): Multiplying out a word in the generators over $\LC(A^{\Z},\F_2)\rtimes\Z$, which maps...
#audit_axioms GroupApproximation.Full.SK13.word_multiplies_out
#audit_closed_axioms GroupApproximation.Full.SKRoot.cor_wp_proof

-- 5092adf162d8, tex l.696–698 (cor:wp): The word is trivial in $G_X$ if and only if the tables of its difference from $I_3$ v...
#audit_axioms GroupApproximation.Full.SK13.wp_reduces_to_language
#audit_axioms GroupApproximation.SimpleKazhdanSofic.PrintedWordProblemReducesToLanguage
#audit_axioms GroupApproximation.SimpleKazhdanSofic.printedWordProblemReducesToLanguage
#audit_axioms GroupApproximation.CylinderTables.matEval_eq_one_iff_language
#audit_axioms GroupApproximation.CylinderTables.eval_eq_zero_iff_language
#audit_axioms GroupApproximation.CylinderTables.turingReducible_of_wordTables
#audit_axioms GroupApproximation.OracleTruthTable.turingReducible_of_truthTable
-- (1 further declaration(s) of this row are audited above)

-- 229c4a7b2e24, tex l.698–700 (cor:wp): Conversely, by~\eqref{eq:elementary} a word for $e_{12}(\prod_{t<m}u^{-t}e_{v_t}u^t)$...
#audit_axioms GroupApproximation.Full.SK13.language_reduces_to_wp
#audit_axioms GroupApproximation.SimpleKazhdanSofic.PrintedLanguageReducesToWordProblem
#audit_axioms GroupApproximation.SimpleKazhdanSofic.printedLanguageReducesToWordProblem
#audit_axioms GroupApproximation.SimpleKazhdanSofic.LanguageReduction.cylinderWord
#audit_axioms GroupApproximation.SimpleKazhdanSofic.LanguageReduction.wordValue_cylinderWord_eq_one_iff
#audit_axioms GroupApproximation.SimpleKazhdanSofic.LanguageReduction.primrec_cylinderWord
-- (1 further declaration(s) of this row are audited above)

-- 5959e4fd6209, tex l.702–707 (cor:wp): For irrational $\alpha\in(0,1)$ let $X_\alpha$ be the infinite minimal Sturmian subsh...
#audit_axioms GroupApproximation.Full.SK13.sturmian_infinite_minimal
#audit_axioms GroupApproximation.Full.SK13.every_degree_sturmian
#audit_axioms GroupApproximation.SimpleKazhdanSofic.sturmianCoding
#audit_axioms GroupApproximation.SimpleKazhdanSofic.sturmianSubshift
#audit_axioms GroupApproximation.SimpleKazhdanSofic.sturmianCoding_eq_floor_sub
#audit_axioms GroupApproximation.SimpleKazhdanSofic.PrintedSturmianSubshiftInfiniteIsMinimal
#audit_closed_axioms GroupApproximation.SimpleKazhdanSofic.printedSturmianSubshiftInfiniteIsMinimal
#audit_closed_axioms GroupApproximation.SimpleKazhdanSofic.printedSturmianSubshiftClosureOfCodings
#audit_axioms GroupApproximation.SimpleKazhdanSofic.PrintedSturmianCodingArc
#audit_closed_axioms GroupApproximation.SimpleKazhdanSofic.printedSturmianCodingArc
-- (1 further declaration(s) of this row are audited above)

-- aa090b172df4, tex l.708–711 (cor:wp): Passing to the closure adds no words, so the words of length $m$ of $X_\alpha$ are th...
#audit_axioms GroupApproximation.Full.SK13.sturmian_language_reduces_to_slope
#audit_axioms GroupApproximation.SimpleKazhdanSofic.language_sturmianSubshift
#audit_axioms GroupApproximation.SimpleKazhdanSofic.PrintedSturmianEndpointsDetermineWords
#audit_closed_axioms GroupApproximation.SimpleKazhdanSofic.printedSturmianEndpointsDetermineWords
#audit_axioms GroupApproximation.SimpleKazhdanSofic.PrintedSlopeComputesSturmianLanguage
#audit_axioms GroupApproximation.SimpleKazhdanSofic.SturmianComputability.printedSlopeComputesSturmianLanguage
-- (1 further declaration(s) of this row are audited above)

-- 4ee0770eb47c, tex l.711–712 (cor:wp): Such a word has $\lfloor\theta+m\alpha\rfloor$ ones, within $1$ of $m\alpha$, so $L(X...
#audit_axioms GroupApproximation.Full.SK13.slope_reduces_to_sturmian_language
#audit_axioms GroupApproximation.Full.SK13.sturmian_language_equiv_slope
#audit_axioms GroupApproximation.SimpleKazhdanSofic.PrintedSturmianOnesWithinOne
#audit_closed_axioms GroupApproximation.SimpleKazhdanSofic.printedSturmianOnesWithinOne
#audit_axioms GroupApproximation.SimpleKazhdanSofic.PrintedSturmianLanguageComputesSlope
#audit_axioms GroupApproximation.SimpleKazhdanSofic.SturmianComputability.printedSturmianLanguageComputesSlope
-- (1 further declaration(s) of this row are audited above)

-- a686ac809830, tex l.712–715 (cor:wp): Every $D\subseteq\mathbb N$ has the degree of $[0;1+\chi_D(0),1+\chi_D(1),\dots]$, si...
#audit_axioms GroupApproximation.Full.SK13.continued_fraction_representative
#audit_axioms GroupApproximation.SimpleKazhdanSofic.PrintedContinuedFractionRepresentative
#audit_closed_axioms GroupApproximation.SimpleKazhdanSofic.printedContinuedFractionRepresentative
#audit_axioms GroupApproximation.SimpleKazhdanSofic.ContinuedFractionOracle.charOracle_turingReducible_slopeOracle
#audit_axioms GroupApproximation.SimpleKazhdanSofic.ContinuedFractionOracle.slopeOracle_turingReducible_charOracle
#audit_axioms GroupApproximation.SimpleKazhdanSofic.ContinuedFractionExpansion.isContinuedFractionOf_tail
#audit_axioms GroupApproximation.SimpleKazhdanSofic.ContinuedFractionExpansion.irrational_tail
-- (1 further declaration(s) of this row are audited above)

-- ebffe49fd098, tex l.716–719 (cor:wp): If a finitely generated group $H$ embeds in a finitely generated group $G$, a word fo...
-- (2 further declaration(s) of this row are audited above)

-- af3a1cf3d48e, tex l.719–721 (cor:wp): By a construction of Sacks, the Turing degrees contain an antichain of size continuum...
#audit_axioms GroupApproximation.Full.SK13.turing_antichain_continuum
#audit_axioms GroupApproximation.SimpleKazhdanSofic.PrintedTuringAntichainContinuum
#audit_closed_axioms GroupApproximation.SimpleKazhdanSofic.printedTuringAntichainContinuum
#audit_axioms GroupApproximation.OracleUse.exists_turing_antichain_continuum
#audit_axioms GroupApproximation.OracleUse.not_turingReducible_branchSet
#audit_axioms GroupApproximation.OracleUse.exists_diag
#audit_axioms GroupApproximation.OracleUse.mem_eval_of_agreeBelow
#audit_axioms GroupApproximation.SimpleKazhdanSofic.LEFCorollaries.manuscriptSentence_sacksAntichainGroups
-- (2 further declaration(s) of this row are audited above)

-- e19e0d3328ad, tex l.730–732 (sec:questions): No group in Theorem~\ref{thm:general}\textup{(b)} is finitely presented: a finitely p...
#audit_axioms GroupApproximation.Full.SK14.printedGeneralNotFinitelyPresented
#audit_axioms GroupApproximation.Full.SK14.not_isFinitelyPresented_general
#audit_axioms GroupApproximation.Full.SK14.isResiduallyFinite_of_isFinitelyPresented_of_isLEF
#audit_axioms GroupApproximation.Full.SK14.not_isResiduallyFinite_of_isSimpleGroup_of_infinite
#audit_closed_axioms GroupApproximation.Full.SKRoot.sec_questions
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.AbstractIntro.manuscriptSentence_generalLimitsNotFinitelyPresented
#audit_closed_axioms GroupApproximation.SimpleKazhdanSofic.printedFinitelyPresentedLEFResiduallyFinite

-- b3fbc4494a6c, tex l.735–738 (sec:questions): A sofic example would not be LEF, and it would answer Open problem~6.1 of Alekseev an...
#audit_axioms GroupApproximation.Full.SK14.manuscriptSentence_soficExampleNotLEF_answersAlekseevThom
#audit_closed_axioms GroupApproximation.Full.SK14.printedSoficKazhdanExampleNotLEF
#audit_axioms GroupApproximation.Full.SK14.IsAlekseevThomExample
#audit_closed_axioms GroupApproximation.SimpleKazhdanSofic.printedSoficKazhdanExampleNotLEF
-- (1 further declaration(s) of this row are audited above)

