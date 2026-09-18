import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.A2Endpoint.Endpoint
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.A2Endpoint.ThomGroup
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.A2Kirchberg.Theorem
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.A2LocalLifting.Factorization
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.A2LocalLifting.Property
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.BrownROmega.Endpoints
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.Definitions.MarkedGroups
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.Definitions.SoficPrinted
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LEFCorollaries.RecursiveHost
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LEFCorollaries.TuringDegree
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.MainTheorem.Endpoints
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.MainTheorem.ProofIngredients
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.Root.Intro
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.Root.Main
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.WordProblems.Endpoints
import GroupApproximation.Manuscript.SimpleKazhdanSofic.MainAssembly
import GroupApproximation.Manuscript.SimpleKazhdanSofic.SimpleKazhdanSoficMainClosed
import GroupApproximation.Manuscript.SimpleKazhdanSofic.ThmMainA.MarkedGroups
import GroupApproximation.Manuscript.SimpleKazhdanSofic.ToeplitzAnswer
import GroupApproximation.Manuscript.SimpleKazhdanSofic.TuringHost.Sentence
import GroupApproximation.Meta.AxiomGuard

/-!
# Attestation of the abstract, the introduction and thm:main (tex l.33–150)

Attestation of the `formalized` rows of `metadata/SK_SENTENCE_CENSUS.tsv` whose sentence starts at
`simple_kazhdan_sofic_group.tex` l.33–150 (census at manuscript commit 22cdba8c): 21 rows, 47 distinct
declarations.  Every declaration a row lists is audited here, grouped under its row, so that one build of
this module checks the axiom closure of the whole range at once.

* `#audit_closed_axioms` for theorems that take no input (the statement is a closed proposition);
* `#audit_axioms` for everything else: theorems whose inputs are the printed hypotheses of their sentence,
  definitions and structures.

Both fail the build on any axiom outside `propext`, `Classical.choice` and `Quot.sound`.  The signatures
were read by hand.  Two rows also list an `_of_` form that takes owed input:
`printedGXAnswersBrownOzawaPestov_of_main` (row 93bcebbc8293, input: the main theorem) and
`printedSimpleKazhdanSoficMain_of_pieces` (row 8e2fecfd278a, input: its four pieces).  Each of these rows
also lists the closed endpoint (`printedSimpleKazhdanSoficMain`, resp. `Full.SKRoot.thm_main`), which is
audited here, so the rows are closed.  No other declaration takes a `…Statement` or an owed proposition.
A declaration listed by several rows is audited at its first row only.
-/

-- 2e0bf7506f2a, tex l.33–34: Infinite simple groups with property~\textup{(T)} can be limits of finite simple groups.
#audit_closed_axioms GroupApproximation.Full.SK05.printedMainTheoremSK01
#audit_axioms GroupApproximation.Full.SK05.main_printed_sk01
#audit_axioms GroupApproximation.Full.SK13.sturmian_infinite_minimal

-- 4d5974e8776d, tex l.34–38: For every infinite minimal subshift $X$, the group $G_X=\EL_3(\LC(X,\F_2)\rtimes\Z)$ ...
#audit_closed_axioms GroupApproximation.Full.SK06.exists_gx_brownForm
-- (2 further declaration(s) of this row are audited above)

-- 93bcebbc8293, tex l.38–40: This answers the question of Brown and Ozawa whether an infinite simple Kazhdan group...
#audit_axioms GroupApproximation.Full.SK01.printedIsHyperlinear_of_isSofic
#audit_closed_axioms GroupApproximation.SimpleKazhdanSofic.printedBrownOzawaPestovAnswer
#audit_axioms GroupApproximation.SimpleKazhdanSofic.printedGXAnswersBrownOzawaPestov_of_main
#audit_closed_axioms GroupApproximation.SimpleKazhdanSofic.toeplitzSubshift_isMinimal
#audit_closed_axioms GroupApproximation.SimpleKazhdanSofic.toeplitzSubshift_infinite
#audit_closed_axioms GroupApproximation.SimpleKazhdanSofic.printedSimpleKazhdanSoficMain
-- (2 further declaration(s) of this row are audited above)

-- ea436a85317e, tex l.41–45: A finitely generated group is LEF if and only if it is a subgroup of an infinite, fin...
#audit_axioms GroupApproximation.Full.SK12.corLef_lefIffSubgroupOfSameTuringDegreeHost
#audit_axioms GroupApproximation.Full.SK12.corLef_hostWithSameTuringDegree
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.TuringHost.manuscriptSentence_lefIffSubgroupOfSimpleKazhdanExpanderLimitSameTuringDegree
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.TuringHost.exists_isLEFHost_sameTuringDegree
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.TuringHost.lefIffSubgroupOfSameTuringDegreeHost

-- 11e5734b503c, tex l.45–46: One such host contains every recursively presented finitely generated LEF group.
#audit_axioms GroupApproximation.Full.SK12.corHost_recursivelyPresentedInstances

-- 5b6a5a222cdd, tex l.54–57: Ozawa stated the hyperlinear form in 2003, noting that the full $C^*$-algebra of such...
#audit_axioms GroupApproximation.Full.A2Endpoint.ozawa_not_hasLocalLiftingProperty
#audit_closed_axioms GroupApproximation.Full.SKRoot.intro_ozawa_thom
#audit_axioms GroupApproximation.Full.A2LocalLifting.not_hasLocalLiftingProperty_of_not_hasFactorizationProperty
#audit_axioms GroupApproximation.Full.A2Kirchberg.not_hasFactorizationProperty_of_isSimpleGroup_of_infinite_of_kazhdan
#audit_axioms GroupApproximation.Full.A2LocalLifting.HasLocalLiftingProperty

-- 6e81aea57b64, tex l.57–60: Thom constructed a finitely generated Kazhdan group that is locally embeddable into f...
#audit_axioms GroupApproximation.Full.A2Endpoint.not_hasFactorizationProperty_of_kazhdan_of_not_residuallyFinite
#audit_closed_axioms GroupApproximation.Full.A2Endpoint.exists_fg_kazhdan_lef_not_rf_not_fp_not_simple
#audit_axioms GroupApproximation.Full.A2Endpoint.not_isSimpleGroup_thomGroup_zmod
#audit_axioms GroupApproximation.Full.A2Kirchberg.isResiduallyFinite_of_hasKazhdanPropertyT_of_hasFactorizationProperty
-- (1 further declaration(s) of this row are audited above)

-- b727e9e6c738, tex l.66–67: The groups below answer all three forms of the question positively.
#audit_axioms GroupApproximation.Full.SK06.brownForm_gx
-- (2 further declaration(s) of this row are audited above)

-- 34bf973db4c8, tex l.76–78 (thm:main): is an infinite, finitely generated, simple group with Kazhdan's property~\textup{(T)}...
#audit_axioms GroupApproximation.Full.SK01.IsFiniteSimpleSL3NF2
#audit_closed_axioms GroupApproximation.Full.SKRoot.thm_main
#audit_axioms GroupApproximation.SimpleKazhdanSofic.ThmMainA.IsExpanderLimitOfClass
#audit_axioms GroupApproximation.SimpleKazhdanSofic.ThmMainA.isExpanderLimit_of_isMarkedLimit
-- (2 further declaration(s) of this row are audited above)

-- 8e2fecfd278a, tex l.78–79 (thm:main): So $G_X$ is locally embeddable into finite groups \textup{(LEF)}, sofic and hyperlinear.
#audit_axioms GroupApproximation.Full.SK01.limitsOfFiniteGroupsAreLEF
#audit_axioms GroupApproximation.Full.SK01.printedIsSofic_iff
#audit_axioms GroupApproximation.SimpleKazhdanSofic.PrintedSimpleKazhdanSoficMain
#audit_axioms GroupApproximation.SimpleKazhdanSofic.printedSimpleKazhdanSoficMain_of_pieces
-- (3 further declaration(s) of this row are audited above)

-- 2d5abd159c20, tex l.82–84 (thm:main): In Brown's form, $G_X$ lies in the unitary group of the McDuff factor $L(G_X)\mathbin...
-- (3 further declaration(s) of this row are audited above)

-- b29ef9356be0, tex l.86–86 (thm:main): Here $X$ is a closed shift-invariant set in which every orbit is dense.
#audit_axioms GroupApproximation.Full.SK05.main_printed
#audit_closed_axioms GroupApproximation.Full.SK05.main
-- (1 further declaration(s) of this row are audited above)

-- 4ae0d642c68a, tex l.104–105 (thm:main): Limits of finite groups in the space of marked groups are LEF.
#audit_axioms GroupApproximation.Full.SK01.limitsOfFiniteGroupsAreLEFPrinted
#audit_axioms GroupApproximation.SimpleKazhdanSofic.ThmMainA.manuscriptSentence_limitsOfFiniteGroupsAreLEF
-- (2 further declaration(s) of this row are audited above)

-- f3342a6d3614, tex l.115–117 (thm:main): The ring $\LC(X,\F_2)\rtimes_T\Z$ consists of the finite sums $\sum_jf_ju^j$ with $f_...
#audit_axioms GroupApproximation.Full.SK05.ingredients_propertyT
#audit_axioms GroupApproximation.Full.SK05.IngredientsPropertyT
-- (1 further declaration(s) of this row are audited above)

-- cbcaca37b5ec, tex l.117–119 (thm:main): It is finitely generated, so $G_X$ has Kazhdan's property~\textup{(T)}~\cite{Kazhdan}...
-- (3 further declaration(s) of this row are audited above)

-- a0cfd12d5e67, tex l.120–123 (thm:main): \emph{Simplicity.} A nontrivial normal subgroup contains a nontrivial commutator lyin...
#audit_axioms GroupApproximation.Full.SK05.printedIngredientsSimplicity
#audit_axioms GroupApproximation.Full.SK05.ingredients_normal_contains_copy
-- (1 further declaration(s) of this row are audited above)

-- 510ed3284bf7, tex l.123–124 (thm:main): So it contains this group and with it an elementary matrix, from which minimality giv...
-- (3 further declaration(s) of this row are audited above)

-- c873cc5ffa5b, tex l.125–129 (thm:main): \emph{Finite models.} A periodic sequence of period $N$ approximating $X$ turns the s...
#audit_axioms GroupApproximation.Full.SK05.ingredients_finiteModels
#audit_axioms GroupApproximation.Full.SK05.IngredientsFiniteModels
-- (1 further declaration(s) of this row are audited above)

-- f94577cbbaa3, tex l.129–130 (thm:main): These models make $G_X$ a limit of the groups $\SL_{3N}(\F_2)$ in the space of marked...
-- (2 further declaration(s) of this row are audited above)

-- d6781a70a33e, tex l.131–134 (thm:main): The $\SL_{3N}(\F_2)$ are quotients of one Kazhdan group, $\EL_3$ of a finitely genera...
#audit_axioms GroupApproximation.Full.SK05.printedProofIngredients
-- (2 further declaration(s) of this row are audited above)

-- b02d9a9819dc, tex l.150–156 (thm:main): \draw[gray] (0,0) -- (5.6,0) node[right,black] {$C$}; \foreach \x/\l in {0.3/bV,2.4/V...
#audit_axioms GroupApproximation.Full.SK05.printedFigureA
#audit_axioms GroupApproximation.Full.SK05.printedFigureB
-- (2 further declaration(s) of this row are audited above)

