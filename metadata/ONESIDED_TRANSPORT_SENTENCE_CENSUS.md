# One-sided transport: sentence-level formalization census

An exhaustive, sentence-level sweep of `non_mf_groups_exist.tex`
(*Not Every Group Is MF*) from `\begin{abstract}` to
`\section*{Acknowledgments}`, against the Lean development.  The current
manuscript has 1362 lines; the direct simplicity proof and every later row have
been re-keyed to the current text, and every status and declaration below has
been rechecked against the current Lean tree.

This is **not** `ONESIDED_TRANSPORT_LEDGER.md`.  That file has one row per
`\label{...}` (44 rows) and answers "is the numbered statement carried?".  This
file has one row per *assertion*, including every displayed equation and every
declarative prose sentence inside a proof, and answers "is the sentence
carried?".  Proof-internal sentences are where a formalization leaks, because a
Lean proof that reaches the same conclusion by a different route leaves them
uncarried while the ledger stays green.

## Conventions

* **Short names.**  A bare `foo` is
  `GroupApproximation.Manuscript.OneSidedMFRadical.foo`.  `RTE.foo` is
  `...OneSidedMFRadical.RankTwelveEndpoint.foo`.  A dotted `Ns.foo` is
  `GroupApproximation.Ns.foo`.  Every declaration named below was grep-verified
  to exist in the tree at the time of writing.
* **`CARRIED`** — a named declaration proves the assertion (possibly as one
  conjunct of a packaged `Prop`).
* **`PARTIAL`** — a weaker, more special, or differently-routed declaration
  exists.  The exact weakening is stated in the row.
* **`MISSING`** — no declaration states the assertion.  A `MISSING` row whose
  *enclosing* numbered statement is `CARRIED` is flagged as such: the paper does
  not depend on it beyond the theorem, but the sentence itself is unformalized.
* **`CITED`** — a literature input with no in-repo route.  The paper is named.

* **Two radicals.**  `manuscriptCoronaMFResidual` is the printed
  natural-dimension `Rad_MF`; `actualCoronaMFResidual` is the basis-free one.
  They are equal (`Sofic.manuscriptCoronaMFResidual_eq_actualCoronaMFResidual`),
  so a row carried by either is carried.

## Status counts

| Status | Rows |
| --- | --- |
| `CARRIED` | 242 |
| `PARTIAL` | 34 |
| `MISSING` | 12 |
| `CITED` | 6 |
| **Total** | **294** |

**Snapshot.**  Counts are as of the working tree containing
`Manuscript/OneSidedMFRadical/{PrintedDefinitions, PrintedLeavittEquations,
PrintedRemarks, ClosurePullback, TransportAssembly, CountableNonMF,
RankTwelveSimplicity, HeadlineTheorem}.lean`, together with
`Leavitt/{BinaryLeavittSimple, ElementaryTransvectionExtraction,
DiagonalNormalExtraction, CongruenceSubgroups, ExchangePrerequisite}.lean`.
The direct root-extraction route now closes the exact rank-twelve simplicity
claim and the complete headline, and the manuscript itself prints that direct
proof.  The separate congruence-subgroup development is retained as an
optional formalization around Preusser's general theorem; the printed
simplicity proof no longer uses it.

Counted by the row's leading status word.  Six rows carry a compound status:
#91, #92, #95, #96, #139, and #227 are `PARTIAL` *and* name a citation, and are
counted as `PARTIAL`; they are represented in the **CITED** section below.
Several rows name a citation whose manuscript-specialized mathematical content
is discharged in-repo, notably #74, #93, #94, #218, #228, and #274.

All 15 numbered manuscript statements are now `CARRIED`.  Of the 12 `MISSING`
rows, **6 are proof-internal to a numbered statement carried by a different
Lean route** (#31, #35, #36, #141, #173, #224), and **6 belong only to the
printed corner-Kazhdan-inequality proof of `thm:normal-kazhdan` plus its
faithful-representation bridge** (#129, #177, #178, #179, #180, #181).  The
theorem itself is carried by the moving-corner/`WeakMF` route.  Preusser appears
only as historical context in #95; direct Leavitt coefficient separation
proves simplicity without his theorem.  See the ranked list after the table.

---

## §0 Abstract (ll. 61–74)

| # | tex line | Claim (verbatim or tight paraphrase) | Lean declaration | Status |
| --- | --- | --- | --- | --- |
| 1 | 62–63 | "Finite-dimensional unitary matrices do not model every countable group in the operator-norm limit." | `manuscriptBinaryLeavittFullRadical` (clause `¬ IsCDEOperatorMF H`) | CARRIED |
| 2 | 63–65 | The MF radical is "the elements sent to the identity by every homomorphism into every norm matrix corona". | `Sofic.manuscriptCoronaMFResidual` | CARRIED |
| 3 | 65–67 | "a one-sided self-compression of a property (T) subgroup forces a canonically defined normal subgroup into the MF radical" | `manuscriptOneSidedCompressionCriterion` (clause 1) | CARRIED |
| 4 | 67 | "Normal generation can then force the MF radical to be the whole group." | `manuscriptOneSidedCompressionCriterion` (clause 3) | CARRIED |
| 5 | 67–69 | "We realize this situation for an elementary group over the binary Leavitt algebra." | `manuscriptBinaryLeavittFullRadical` | CARRIED |
| 6 | 69 | "The resulting group is simple" | `RTE.manuscriptPropositionSimple` | CARRIED |
| 7 | 69 | "…has property (T)" | `RTE.hasKazhdanPropertyT` | CARRIED |
| 8 | 69–70 | "every homomorphism from it to an MF group is trivial" | `manuscriptBinaryLeavittFullRadical` (clause 6) | CARRIED |
| 9 | 70–71 | "In particular, not every countable group is MF." | `manuscriptBinaryLeavittFullRadical` cl. 7; `CountableNonMF.manuscriptNotEveryCountableGroupIsMF`, `manuscriptCountableNonMFGroupExists` | CARRIED |
| 10 | 71–73 | "an amalgamated-product construction realizes any chosen countable group as the quotient detected by all homomorphisms to MF groups" | `manuscriptPrescribedMFQuotients` | CARRIED |

## §1 Introduction — definitions (ll. 77–171)

| # | tex line | Claim | Lean declaration | Status |
| --- | --- | --- | --- | --- |
| 11 | 77–79 | "A countable group is MF if it embeds in the unitary group of a norm matrix corona." | `Sofic.IsCDEOperatorMF` | CARRIED |
| 12 | 108–112 | Display: `Q_d = ∏_n M_{d_n}(C) / ⊕_n M_{d_n}(C)`. | `Analysis.NormMatrixCStarCorona` | CARRIED |
| 13 | 118–122 | Display: `⊕_n M_{d_n}(C) = {(x_n) : ‖x_n‖ → 0}`. | `Analysis.IsNullMatrixSequence` (at `cofinite`); `PrintedDefinitions.manuscriptCoronaDenominator`, `normMatrixCStarCoronaMk_eq_zero_iff_tendsto` | CARRIED |
| 14 | 123 | "is the `c_0`-direct sum" | same as #13 (`PrintedDefinitions.manuscriptCoronaDenominator`) | CARRIED |
| 15 | 123–126 | "Equivalently, an MF group admits finite-dimensional unitary models whose multiplicative defects tend to zero in operator norm and which asymptotically separate its nonidentity elements." | `Sofic.isCDEOperatorMF_iff_isOperatorMF`; `PrintedDefinitions.manuscriptMFUnitaryModels`, `isCDEOperatorMF_exists_separating_unitary_models` | CARRIED |
| 16 | 127–129 | "Throughout, *MF group* means this operator-norm notion of Carrión–Dadarlat–Eckhardt and Korchagin." | — | CITED (CDE; Korchagin) |
| 17 | 153–157 | Display: `Rad_MF(G) = ⋂_d ⋂_π ker π`. | `Sofic.manuscriptCoronaMFResidual` | CARRIED |
| 18 | 158 | "The group `G` is MF precisely when `Rad_MF(G)` is trivial." | `Sofic.isCDEOperatorMF_iff_actualCoronaMFResidual_eq_bot` | CARRIED |
| 19 | 158–160 | "If `Rad_MF(G)=G`, every homomorphism from `G` to an MF group is trivial." | `manuscriptFullRadicalKillsMFTargets` | CARRIED |
| 20 | 162–166 | Display: `cl_MF^G(N) = ⋂{ker f : N ≤ ker f, f : G → M, M MF}`. | `literalMFClosure`, `LiteralMFKernels` | CARRIED |
| 21 | 167 | "The image of a corona homomorphism from `G` is countable and is itself MF" | `Sofic.CoronaImageNormalKazhdan.nk_02_countable_mf_image`; `PrintedDefinitions.coronaImage_countable`, `coronaImage_isOperatorMF`, `manuscriptCoronaImagesAndTargets` | CARRIED |
| 22 | 168 | "conversely, every MF target embeds in a norm matrix corona" | `PrintedDefinitions.isCDEOperatorMF_exists_coronaEmbedding`, `isCDEOperatorMF_of_coronaEmbedding`, `manuscriptCoronaImagesAndTargets` | CARRIED |
| 23 | 169 | `Rad_MF(G) = cl_MF^G(1)` | `literalMFClosure_bot`, `manuscriptMFRadicalIsLiteralClosureOfTrivial` | CARRIED |
| 24 | 170–171 | "`G/N` is MF precisely when `cl_MF^G(N)=N`" | `isCDEOperatorMF_quotient_iff_literalMFClosure_eq` | CARRIED |

## §1 `prop:mf-residual-calculus` (ll. 173–183) and its proof (ll. 185–209)

| # | tex line | Claim | Lean declaration | Status |
| --- | --- | --- | --- | --- |
| 25 | 174–175 | "`Rad_MF(G)` is fully invariant" | `manuscriptMFResidualCalculusLiteral` cl. 1; `Sofic.map_actualCoronaMFResidual_le` | CARRIED |
| 26 | 175 | "the quotient `G/Rad_MF(G)` is MF" | `Sofic.actualCoronaMFQuotient_isCDEOperatorMF` | CARRIED |
| 27 | 176–181 | Display: `G/N` MF `⟺ cl_MF^G(N)=N`. | `manuscriptMFResidualCalculusLiteral` cl. 3; `Sofic.actualCoronaMFClosure_eq_self_iff` | CARRIED |
| 28 | 182 | "In particular, `G` is MF if and only if its MF radical is trivial." | `manuscriptMFResidualCalculusLiteral` cl. 4 | CARRIED |
| 29 | 186 | "An intersection of kernels is normal." | `literalMFClosure_normal` (instance); `PrintedRemarks.manuscriptIntersectionOfKernelsIsNormal`, `sInf_normal_of_forall_normal`, `iInf_ker_normal` | CARRIED |
| 30 | 186–189 | "If `α` is an endomorphism, `x ∈ Rad_MF(G)`, `π` a corona homomorphism, then `π∘α` kills `x`; hence full invariance." | `Sofic.map_actualCoronaMFResidual_le` — its proof is literally `intro rho; exact hx d hd (rho.comp f)` | CARRIED |
| 31 | 191–192 | "enumerate the nonidentity elements of `G/R` as `(x_j)`, and enumerate the pairs in `(G/R)²`" | — | MISSING (proof-internal; #37 is carried by a different route) |
| 32 | 192–194 | "For each `x_j`, the definition of `R` supplies a corona homomorphism whose value at `x_j` has positive distance from the identity." | `Sofic.exists_normMatrixCoronaRepresentation_ker_eq_normMFResidual` | PARTIAL — gives one universal representation with `ker = R`, not one detector per `x_j`, and no quantitative "positive distance" |
| 33 | 194–195 | "Every such homomorphism kills `R` and therefore descends to `G/R`." | `Sofic.normMFResidual_normMFQuotient_eq_bot` | PARTIAL — the descent is packaged in the quotient construction, not stated for an arbitrary detector |
| 34 | 195–196 | "Choose coordinate unitary lifts, using polar correction as in Lemma `lem:central-corona-corner`." | `Analysis.CollapseUnitaryLift.liftFam`, `Analysis.PolarLiftingGeneralCStar.polarUnitary` | PARTIAL — the machinery exists and is used elsewhere; it is not what proves #37 |
| 35 | 196–201 | "At stage `n`, take a direct sum of one coordinate from each of the first `n` models. Choose each coordinate far enough out that the first `n` multiplication defects are at most `1/n` and the designated value at `x_j` retains at least half of its corona-norm separation." | — | MISSING (proof-internal) |
| 36 | 201–202 | "Such coordinates exist arbitrarily far out: the defects converge to zero, while the quotient norm is a limsup." | — | MISSING (proof-internal; no quotient-norm-as-limsup lemma is used on this route) |
| 37 | 202–204 | "The resulting operator-norm asymptotic representation detects every `x_j`, so its corona homomorphism is faithful on `G/R`. Thus `G/R` is MF." | `Sofic.actualCoronaMFQuotient_isCDEOperatorMF` | CARRIED (via ultraproducts, not via the printed diagonal sum) |
| 38 | 206–208 | "Applied to `G/N`, the same argument says that `G/N` is MF exactly when the intersection of the kernels of all MF-target maps killing `N` is `N`." | `Sofic.actualCoronaMFClosure_eq_self_iff`, `isCDEOperatorMF_quotient_iff_literalMFClosure_eq` | CARRIED |

## §1 The compression–centralizer defect (ll. 213–242)

| # | tex line | Claim | Lean declaration | Status |
| --- | --- | --- | --- | --- |
| 39 | 225 | `Comp_G(L) = {u ∈ G : uLu^{-1} ≤ L}` | `Criterion.compressionSet` | CARRIED |
| 40 | 235–241 | `eq:intrinsic-defect`: `𝔇_G(L) = ⟨⟨[ucu^{-1},ℓ] : u ∈ Comp_G(L), c ∈ C_G(L), ℓ ∈ L⟩⟩_G` | `printedDefect`, `printedDefectSet` | CARRIED |
| 41 | 242 | "This subgroup depends only on the pair `(G,L)`." | `printedDefect` is a function of `G` and `L` alone | CARRIED (definitional) |

## §1 Theorem A `thm:compression-criterion` (ll. 244–261)

| # | tex line | Claim | Lean declaration | Status |
| --- | --- | --- | --- | --- |
| 42 | 246–256 | `G` countable, `L` with (T), `K ⊴ G` with (T) and `K ≤ 𝔇_G(L)` ⟹ `K ≤ Rad_MF(G)`. | `manuscriptOneSidedCompressionCriterion` cl. 1 | CARRIED |
| 43 | 257 | "a nontrivial such `K` makes `G` non-MF" | `manuscriptOneSidedCompressionCriterion` cl. 2 | CARRIED |
| 44 | 257–259 | "if `G` has property (T) and `𝔇_G(L)=G`, then `Rad_MF(G)=G`" | `manuscriptOneSidedCompressionCriterion` cl. 3 | CARRIED |
| 45 | 259–260 | "Every finite-dimensional linear representation of `G` over every field kills `𝔇_G(L)`." | `manuscriptPrintedDefectFiniteDimensionalSterility` | CARRIED |

## §1 Proof sketch of Theorem A (ll. 263–277)

| # | tex line | Claim | Lean declaration | Status |
| --- | --- | --- | --- | --- |
| 46 | 263–266 | "every generator of `𝔇_G(L)` converges to the identity in normalized Hilbert–Schmidt norm in every operator-norm asymptotic representation" | `manuscriptCompressionDefectHSInvisible` | CARRIED |
| 47 | 266–268 | "If the image of `K` in a norm matrix corona were nontrivial, normality would make the projection onto the `K`-fixed vectors commute with the image of `G`." | `Analysis.NormalKazhdanUltraproduct.nk_07_commute_proj` (and `nk_07_omega_commute_proj`) | CARRIED |
| 48 | 268–269 | "Compression to its complementary corner would give another operator-norm asymptotic representation." | `manuscriptCentralCoronaCorner` | CARRIED |
| 49 | 269–271 | "the Kazhdan inequality would keep some element of `K` a fixed positive Hilbert–Schmidt distance from the identity" | `Sofic.NormalKazhdanCompressionObstruction.not_isWeakMF_of_normalKazhdan_le_defect` + `Sofic.InternalRadicalGap` | PARTIAL — the Lean gap is the moving-corner/`WeakMF` argument, not the printed corner Kazhdan inequality (see #177–#182) |
| 50 | 271–272 | "This contradiction proves the criterion." | `manuscriptOneSidedCompressionCriterion` | CARRIED |
| 51 | 272–273 | "In finite dimension, Theorem `thm:commutant` proves the corresponding statement over every field without property (T)." | `manuscriptFiniteDimensionalCommutantRigidity` | CARRIED |
| 52 | 275–277 | "Whether every countable group is MF was asked in the group-MF literature and remained open." | — | CITED (CDE; Korchagin; Thom; Shulman) |

## §1 The Leavitt algebra and the elementary group (ll. 291–304)

| # | tex line | Claim | Lean declaration | Status |
| --- | --- | --- | --- | --- |
| 53 | 291–296 | `eq:leavitt`: `L_{F2}(1,2)` is the unital `F_2`-algebra on `s_0,s_1,t_0,t_1` with `t_i s_j = δ_ij`, `s_0t_0+s_1t_1=1`. | `RTE.leavittFamily`; `LeavittFamily` (fields `t0_s0`,`t0_s1`,`t1_s0`,`t1_s1`,`sum_range`); `Leavitt.UniversalLeavitt.BinaryLeavittAlgebra` (over `ZMod 2`) | CARRIED |
| 54 | 302–304 | "write `e_ij(a)=1+aE_ij` and let `EL_n(R)` be the subgroup of `GL_n(R)` generated by the `e_ij(a)`, `i≠j`" | `Leavitt.elementaryUnit`, `Leavitt.elementaryGroup`, `Leavitt.elementaryRoot` | CARRIED |

## §1 Theorem B `thm:headline` (ll. 306–326)

| # | tex line | Claim | Lean declaration | Status |
| --- | --- | --- | --- | --- |
| 55 | 313 | `H = EL_12(R)` is nontrivial. | `RTE.nontrivial` | CARRIED |
| 56 | 313 | `H` is **simple**. | `RTE.manuscriptPropositionSimple`; `manuscriptBinaryLeavittHeadline` | CARRIED |
| 57 | 313–314 | `H` has property (T). | `RTE.hasKazhdanPropertyT` (`Steinberg.BinaryLeavitt.elementaryBase_hasKazhdanPropertyT`) | CARRIED |
| 58 | 321–323 | `Rad_MF(H) = H`. | `RTE.rankTwelve_actualCoronaMFResidual_eq_top` | CARRIED |
| 59 | 324 | "Equivalently, every homomorphism from `H` to an MF group is trivial." | `manuscriptBinaryLeavittFullRadical` cl. 6 | CARRIED (from the full radical, *not* from simplicity as the printed "equivalently" suggests) |
| 60 | 325 | "In particular, `H` is non-MF." | `Sofic.not_isCDEOperatorMF_of_actualCoronaMFResidual_eq_top` | CARRIED |

## §1 The explicit configuration (ll. 328–375)

| # | tex line | Claim | Lean declaration | Status |
| --- | --- | --- | --- | --- |
| 61 | 328–334 | `eq:basic-defect`: `‖V_n([ucu^{-1},ℓ]) − 1‖₂ → 0` for `ℓ ∈ L`. | `manuscriptCompressionDefectHSInvisible` | CARRIED |
| 62 | 341–342 | "Inside `H`, an explicit element `τ` satisfies `τLτ^{-1} ≤ L`." | `RTE.tau_compresses_corner`, `RTE.printedDefectConfiguration` | CARRIED |
| 63 | 342 | "for the upper-left subgroup `L ≅ EL_3(R)`" | `RTE.cornerEmbedding`, `RTE.cornerEmbeddingToCorner_surjective`, `RTE.cornerEmbedding_range` | CARRIED |
| 64 | 342–343 | "The element `c = e_34(1)` centralizes `L`." | `RTE.c_commutes_corner` | CARRIED |
| 65 | 351–353 | Display: `d = e_02(s_1t_1)`. | `RTE.defect`, `RTE.tau_c_commutator_ell` | CARRIED |
| 66 | 354 | "The element `d` is nontrivial" | `RTE.defect_ne_one` | CARRIED |
| 67 | 354–355 | "and `H` is simple, so `d` normally generates `H`" | `RTE.manuscriptPropositionSimple`; `RTE.normalClosure_defect_eq_top` | PARTIAL — both premise and conclusion are proved, but the named normal-closure proof uses the stronger Steinberg root theorem rather than separately encoding this printed inference |
| 68 | 355–356 | "Since `d ∈ 𝔇_H(L)`, simplicity first gives `H ≤ 𝔇_H(L)`" | `RTE.manuscriptPropositionSimple`; `RTE.printedDefect_eq_top_of_configuration` | PARTIAL — the endpoint is proved using the independently available normal generation of `d`; this exact proof-internal inference is not separately named |
| 69 | 356–359 | "thus the compression defect is the ambient Kazhdan group, and Theorem A gives `Rad_MF(H)=H`" | `RTE.residual_eq_top_of_configuration`, `RTE.rankTwelve_actualCoronaMFResidual_eq_top` | CARRIED |
| 70 | 361–363 | "If `ρ : G → GL(V)` with `V` finite-dimensional, conjugation by `ρ(u)` maps the commutant of `ρ(L)` injectively into itself, hence bijectively." | `Criterion.fixedSubmodule_map_eq` | CARRIED |
| 71 | 363 | "Thus `ρ` kills `𝔇_G(L)`." | `manuscriptPrintedDefectFiniteDimensionalSterility` | CARRIED |
| 72 | 364–366 | "if `G` has a faithful finite-dimensional linear representation … then `𝔇_G(L)=1`" | `printedDefect_eq_bot_of_faithful_finiteDimensional` | CARRIED |
| 73 | 366 | "…or is residually finite, then `𝔇_G(L)=1`" | `printedDefect_eq_bot_of_isResiduallyFinite` | CARRIED |
| 74 | 366–367 | "If `G` is amenable, its property-(T) subgroup `L` is finite [BHV]." | `Kazhdan.finite_subgroup_of_isAmenable_of_kazhdan`; `PrintedRemarks.manuscriptPrintedAmenableCaseChain` | CARRIED — proved in-repo; the `BHV` citation is no longer load-bearing |
| 75 | 368 | "then `uLu^{-1}=L`" | `Kazhdan.conj_image_eq_of_isAmenable_of_kazhdan`; `PrintedRemarks.manuscriptPrintedAmenableCaseChain` | CARRIED |
| 76 | 368–370 | "so `ucu^{-1}` centralizes `L` for every `u ∈ Comp_G(L)`" | `Kazhdan.commute_conj_of_isAmenable_of_kazhdan`; `PrintedRemarks.manuscriptPrintedAmenableCaseChain` | CARRIED |
| 77 | 370 | "and again `𝔇_G(L)=1`" | `Kazhdan.printedDefect_eq_bot_of_isAmenable_of_kazhdan`; `manuscriptAmenableKazhdanSterility`; `PrintedRemarks.manuscriptPrintedAmenableCaseChain` | CARRIED |
| 78 | 372–375 | "The argument is specific to operator-norm approximation. It does not prove that `H` is nonsofic or nonhyperlinear: normalized Hilbert–Schmidt approximations do not provide the operator-norm control used to construct the conjugation representation in Theorem `thm:transport`." | `PrintedRemarks.manuscriptFullRadicalsDoNotEntailNonsoficity` (four clauses: a full `Rad_MF` and a full `R_(∞→2)` each fail to entail non-soficity and non-hyperlinearity), `manuscriptSoficityIsNotObstructedByFullRadicals` | CARRIED |

## §1 Theorem C `thm:prescribed-quotients` (ll. 377–407)

| # | tex line | Claim | Lean declaration | Status |
| --- | --- | --- | --- | --- |
| 79 | 380–382 | "`B` countable with `Rad_MF(B)=B`, `1≠d ∈ B` normally generating `B`; put `A=⟨d⟩`." | `Sofic.MFCamouflage.Edge`, `MFCamouflage.edgeIsCyclic` | CARRIED |
| 80 | 383–385 | Display: `W_Q = B *_A (Q × A)`. | `Sofic.MFCamouflage.Camouflage` | CARRIED |
| 81 | 386–387 | "the map `π_Q : W_Q → Q` which kills `B` and projects the second vertex group onto `Q` is a split epimorphism" | `MFCamouflage.projection_blackHole`, `projection_productVertex`, `projection_surjective`, `projection_comp_visible` | CARRIED |
| 82 | 394–397 | Display: `Rad_MF(W_Q) = π_Q^{-1}(Rad_MF(Q))`. | `MFCamouflage.actualCoronaMFResidual_eq_comap` | CARRIED |
| 83 | 398 | "The group `W_Q` is non-MF." | `manuscriptPrescribedMFQuotients` cl. 3 | CARRIED |
| 84 | 398–401 | "If `Q` is MF, then `Rad_MF(W_Q)=ker π_Q = ⟨⟨d⟩⟩_{W_Q}`." | `MFCamouflage.actualCoronaMFResidual_eq_ker`, `MFCamouflage.projection_ker_eq_normalClosure` | CARRIED |
| 85 | 402–406 | "precomposition with `π_Q` induces a bijection `Hom(Q,M) → Hom(W_Q,M)` for every MF group `M`" | `MFCamouflage.cdeMF_precomp_bijective` | CARRIED |

## §1 Relation to prior work (ll. 400–437)

| # | tex line | Claim | Lean declaration | Status |
| --- | --- | --- | --- | --- |
| 86 | 402–406 | "The group-MF framework used here is developed by Carrión–Dadarlat–Eckhardt and Korchagin; permanence results are due to Shulman." | — | CITED (CDE; Korchagin; Shulman) |
| 87 | 406–408 | "The operator-norm case remained open after non-approximability had been established for finite Schatten norms." | — | CITED (DGLT; LubotzkyOppenheim; Thom) |
| 88 | 409–410 | "Bachner–Dogon–Lubotzky study an operator–Hilbert–Schmidt stability condition as a possible source of non-MF groups." | — | CITED (BDL) |
| 89 | 411–412 | Operator-norm control makes coordinatewise conjugation a representation in a second norm matrix corona. | `Analysis.AdjointDefectEstimate.adConj_asymptoticallyMultiplicative`, `printedAdjointParagraph` | CARRIED |
| 90 | 412–415 | Its Kazhdan projection controls the Hilbert–Schmidt asymptotic commutant, and Section 4 puts a normal Kazhdan subgroup in the MF radical. | `Sofic.UltraproductKazhdanProjection.kt_08_kazhdan_projection`; `Sofic.ultraproductKazhdanTransport`; `manuscriptNormalKazhdanRadical` | CARRIED |
| 91 | 417–423 | Tseng's related result makes the Kazhdan projection infinite under a proper one-sided compression and obstructs MF-ness of the full group `C*`-algebra; the present proof instead uses corona stable finiteness to obstruct the group-MF property. | `manuscriptNormMatrixCoronaStableFinite`; `manuscriptOneSidedKazhdanTransport`; `manuscriptNormalKazhdanRadical` | PARTIAL / CITED (Tseng) — the present comparison endpoint is formalized; Tseng's literature theorem is not |
| 92 | 425–428 | Leavitt introduced `L_K(1,n)` as nonunique-rank rings; the binary algebra is purely infinite simple. | `LeavittFamily.rankSuccEquiv`; `BinaryLeavitt.hasSingleSandwichDivision`; `HasSingleSandwichDivision.isSimpleRing` | PARTIAL / CITED (Leavitt; AbramsAranda) — related positive-rank equivalences, the exact sandwich property, and ring simplicity are formalized; the historical module-rank statement and a general pure-infiniteness predicate are not |
| 93 | 428 | "hence an exchange ring" | `ExchangePrerequisite.HasRightExchange`; `BinaryLeavitt.hasRightExchange` | CARRIED |
| 94 | 429 | "and its center is the base field" | `BinaryLeavitt.center_eq_bot`, `eq_smul_one_of_central` | CARRIED |
| 95 | 429–432 | Preusser gives general normal-subgroup theorems over exchange rings; this proof instead extracts an elementary root directly. | `rootDetection_of_leavittFamily`; `RTE.normalRootDetection`; `RTE.manuscriptPropositionSimple` | PARTIAL / CITED (Preusser) — the direct route is formalized; the general literature attribution is not |
| 96 | 433–435 | Ershov–Jaikin-Zapirain give property (T) for `EL_n(R)` when `n≥3` and `R` is finitely generated unital associative. | `Steinberg.BinaryLeavitt.elementaryBase_hasKazhdanPropertyT` proves the case used | PARTIAL / CITED (EJZ) — the general statement is not in the tree |
| 97 | 436–437 | Related rigidity results for metric approximations of Kazhdan groups appear in the cited literature. | — | CITED (KT19; AlekseevThom; Dadarlat) |

## §2 `thm:commutant` (ll. 437–450) and its proof (ll. 452–469)

| # | tex line | Claim | Lean declaration | Status |
| --- | --- | --- | --- | --- |
| 98 | 438–444 | `uLu^{-1} ≤ L` ⟹ `ρ(u)ρ(L)'ρ(u)^{-1} = ρ(L)'` in `End_k(V)`, `V` finite-dimensional over a field `k`. | `manuscriptFiniteDimensionalCommutantRigidity` cl. 1; `Criterion.fixedSubmodule_map_eq` | CARRIED |
| 99 | 445–449 | "Consequently, if `c ∈ C_G(L)`, then `ρ([ucu^{-1},ℓ]) = 1` for `ℓ ∈ L`." | `manuscriptFiniteDimensionalCommutantRigidity` cl. 2; `Criterion.map_compressionCentralizerDefect_generator_eq_one` | CARRIED |
| 100 | 453–460 | The three-line computation `ρ(h)ρ(u)^{-1}xρ(u) = ρ(u)^{-1}ρ(h')xρ(u) = ρ(u)^{-1}xρ(h')ρ(u) = ρ(u)^{-1}xρ(u)ρ(h)`. | inside `Criterion.fixedSubmodule_map_eq` | PARTIAL — no separately named step |
| 101 | 461 | "Thus `ρ(u)^{-1}Cρ(u) ⊆ C`." | inside `Criterion.fixedSubmodule_map_eq` | PARTIAL — no separately named step |
| 102 | 461–463 | "Conjugation by `ρ(u)^{-1}` is injective, and `C` is finite-dimensional. Its restriction to `C` is therefore surjective, so the inclusion is equality." | `PrintedRemarks.commutant_surjective_of_injective`; `Criterion.fixedSubmodule_map_eq` | CARRIED |
| 103 | 463–464 | "Conjugating by `ρ(u)` gives `ρ(u)Cρ(u)^{-1}=C`." | `manuscriptFiniteDimensionalCommutantRigidity` cl. 1 (stated in exactly this direction) | CARRIED |
| 104 | 466–468 | "`ρ(c) ∈ C`, hence `ρ(ucu^{-1}) ∈ C`; it commutes with every `ρ(ℓ)`." | `Criterion.map_compressionCentralizerDefect_generator_eq_one` | CARRIED |
| 105 | 471–473 | "The finite-dimensional hypothesis is essential here. On an infinite-dimensional space an injective endomorphism of the commutant need not be surjective." | `PrintedRemarks.manuscriptCommutantFiniteDimensionalHypothesisIsEssential` cl. 3 — an explicit injective non-surjective `Φ` on `End_C(ℕ → C)` (`shiftConjugation`, `shiftConjugation_injective`, `shiftConjugation_not_surjective`) | CARRIED |
| 106 | 473–475 | "In Section 3 the Kazhdan projection places the analogous endomorphism inside a norm matrix corona, where stable finiteness supplies the missing surjectivity at the level of fixed-space projections." | `manuscriptNormMatrixCoronaStableFinite`; `Sofic.UltraproductKazhdanTransport.kt_10_finiteness_reverses` | CARRIED |

## §3 Setup (ll. 479–501)

| # | tex line | Claim | Lean declaration | Status |
| --- | --- | --- | --- | --- |
| 107 | 479–483 | `‖a‖₂ = tr_d(a*a)^{1/2}`, `tr_d = (1/d)Tr`. | `Sofic.hsLengthSq` (normalized) | CARRIED |
| 108 | 484–489 | Definition of an operator-norm asymptotic representation: `V_n : G → U(d_n)`, `V_n(1)=1`, `‖V_n(gh) − V_n(g)V_n(h)‖ → 0`. | `Sofic.OpAlmostRepresentation` | CARRIED |
| 109 | 490–493 | `K_2(V) = {g : ‖V_n(g) − 1‖₂ → 0}`. | `hsKernel`, `IsHSNull`, `isHSNull_iff_tendsto` | CARRIED |
| 110 | 494–495 | "The operator-norm defects also tend to zero in normalized Hilbert–Schmidt norm" | `Sofic.UltraproductKazhdanTransport.hsNormSq_le_mul_self_l2_opNorm` | CARRIED |
| 111 | 495 | "so `K_2(V)` is a normal subgroup of `G`" | `hsKernel_normal` (instance); `manuscriptShadowResidualIsIntersectionOfHSKernels` cl. 2 | CARRIED |
| 112 | 496–499 | `eq:shadow-residual`: `R_{∞→2}(G) = ⋂_V K_2(V)`. | `opToHSShadowResidual_eq_iInf_hsKernel`; `manuscriptShadowResidualIsIntersectionOfHSKernels` cl. 3 | CARRIED |
| 113 | 500–501 | "An element is universally Hilbert–Schmidt trivial precisely when it belongs to `R_{∞→2}(G)`." | `mem_opToHSShadowResidual_iff_forall_hsKernel` | CARRIED |

## §3 `lem:stable-finite` (ll. 503–510) and its proof (ll. 512–522)

| # | tex line | Claim | Lean declaration | Status |
| --- | --- | --- | --- | --- |
| 114 | 503–508 | "For every sequence `(m_n)`, the norm matrix corona is stably finite." | `manuscriptNormMatrixCoronaStableFinite` cl. 1 | CARRIED |
| 115 | 508–509 | "Consequently, unitarily equivalent projections in a norm matrix corona are equal whenever one is dominated by the other." | `manuscriptNormMatrixCoronaStableFinite` cl. 2 (order written as `q*p=p`) | CARRIED |
| 116 | 513–514 | "Suppose `v*v=1`; let `(x_n)` be a bounded lift. Then `x_n*x_n → 1` in norm." | inside `Analysis.MatrixCoronaFinite.mul_eq_one_symm_matrixCorona` | PARTIAL — no separately named lift-defect lemma |
| 117 | 514–516 | "For all sufficiently large `n`, `x_n` is invertible, and `x_n(x_n*x_n)^{-1/2}` differs from `x_n` by `o(1)`." | `Analysis.PolarLiftingGeneralCStar.polarUnitary`, `norm_polarUnitary_sub_le`; `Analysis.PolarLiftingPrintedSequence` | CARRIED |
| 118 | 516 | "Thus `v` is represented by unitaries and `vv*=1`." | `Analysis.MatrixCoronaFinite.mul_eq_one_symm_matrixCorona` | CARRIED |
| 119 | 516–517 | "The same argument applies to every matrix amplification of the corona." | same declaration, stated for `Matrix (Fin k) (Fin k)` over the corona | CARRIED |
| 120 | 517–519 | "If `A` is a stably finite unital `C*`-algebra, equivalent projections `p ≤ q` satisfy `p=q`." | `Analysis.dedekindFiniteCStar_eq_of_murrayVonNeumannEquiv_of_absorbs` | CARRIED |
| 121 | 519–520 | "if `w*w=q` and `ww*=p`, then `w ∈ qAq` is an isometry in the corner" | `Analysis.CoronaProjectionOrder.cstar_corner_eq_of_isometryPair`, `mul_right_eq_left_mul_of_isometryPair` | CARRIED |
| 122 | 520 | "The corner is finite because `w+(1−q)` is an isometry in `A`." | `Analysis.CoronaProjectionOrder.eq_of_isometryPair_of_absorbs` | PARTIAL — the `w+(1−q)` device is not a named lemma; Lean argues absorption directly |
| 123 | 521 | "Consequently `ww*=q`, and hence `p=q`." | `Analysis.CoronaProjectionOrder.eq_of_isometryPair_of_le` | CARRIED |

## §3 `lem:kazhdan-projection-order` (ll. 524–537) and its proof (ll. 539–553)

| # | tex line | Claim | Lean declaration | Status |
| --- | --- | --- | --- | --- |
| 124 | 526–528 | "`P ∈ B` is the image of the Kazhdan projection under the extension `C*_max(L) → B`." | `Analysis.maximalGroupCStarLift` + `Sofic.UltraproductKazhdanProjection.KazhdanCompressionRep.proj` (`spectralProjection` of the orbit average) | PARTIAL — Lean builds `P` directly in `B` as a spectral projection; there is **no** Kazhdan projection inside `C*_max(L)`, and the printed factorization through `C*_max` is not the route |
| 125 | 529–536 | `Uπ(L)U* ⊆ π(L)` ⟹ `U*PU ≤ P`. | `manuscriptOneSidedKazhdanProjectionOrder` | CARRIED (order stated as the two absorption identities; the module documents the one-line rewrite to `≤`) |
| 126 | 540–542 | "Represent `B` faithfully and nondegenerately on `H`. The represented `P` is the orthogonal projection onto `Fix π(L)`." | `Analysis.KazhdanProjectionOneSidedOrder.invariantProjection_eq_starProjection` | PARTIAL — proved on a Hilbert space; that module deliberately leaves the abstract `C*`-algebra bridge as a hypothesis |
| 127 | 544–549 | "`π(ℓ)U*ξ = U*(Uπ(ℓ)U*)ξ = U*ξ`, because `Uπ(ℓ)U* ∈ π(L)`." | `Analysis.KazhdanProjectionOneSidedOrder.symm_mem_invariantSubmodule_of_compresses`, `symm_mem_of_conj_mem` | CARRIED |
| 128 | 549–551 | "Hence `U*Fix π(L) ⊆ Fix π(L)`, so the range projection `U*PU` is dominated by `P` in `B(H)`." | `Analysis.KazhdanProjectionOneSidedOrder.star_mul_invariantProjection_mul_le`, `conjProjection_invariantProjection_le` | CARRIED |
| 129 | 551–552 | "Faithfulness of the representation gives the same projection inequality in `B`." | — | MISSING — this is exactly the bridge `KazhdanProjectionOneSidedOrder` leaves as a hypothesis; `manuscriptOneSidedKazhdanProjectionOrder` avoids it by using the abstract `kt_09_*` route instead |

## §3 `thm:transport` (ll. 555–571) and its proof (ll. 573–612)

| # | tex line | Claim | Lean declaration | Status |
| --- | --- | --- | --- | --- |
| 130 | 556–570 | Statement: both conjugation directions of the transport. | `manuscriptOneSidedKazhdanTransport`; `TransportAssembly.manuscriptOneSidedKazhdanTransportPackage`, `manuscriptOneSidedKazhdanTransportAnyAmbient` | CARRIED |
| 131 | 574–576 | "Regard `M_{d_n}(C)` as a Hilbert space with its normalized Hilbert–Schmidt inner product, and form the Hilbert-space ultraproduct `K_ω`." | `Sofic.AdjointMatrix.rowVec`/`rowMat`; `Analysis.CollapseUltraproductRepresentation.conjIsometryEquiv` | CARRIED |
| 132 | 576–577 | "Conjugation by the `V_n(g)` defines a unitary representation `σ` of `G` on `K_ω`." | `Analysis.CollapseUltraproductRepresentation.conjRep`; `Sofic.AdjointMatrix.adjoint` | CARRIED |
| 133 | 578–582 | Display: `‖Ad(A) − Ad(B)‖ ≤ 2‖A − B‖` for unitaries `A,B`. | `Sofic.AdjointMatrix.l2_opNorm_conjDouble_sub_le_two`; `Analysis.AdjointDefectEstimate.opNorm_adConj_sub_le_two_mul` | CARRIED |
| 134 | 583–584 | "so the operator-norm multiplicative defects of `(V_n)` also make the conjugation actions multiplicative modulo `c_0`" | `Analysis.AdjointDefectEstimate.adConj_asymptoticallyMultiplicative`; `AdjointMatrix.l2_opNorm_conjDouble_defect_le` | CARRIED |
| 135 | 585 | "The class `ξ=[x_n]_ω` is fixed by `σ(L)`." | `Sofic.KazhdanAsymptoticCommutant.HSSqVanishing` / `IsAsymptoticCommutantOf` (hypothesis of `manuscriptOneSidedKazhdanTransport`) | CARRIED |
| 136 | 587–593 | "`B = ∏_n B(M_{d_n}(C))/⊕_n B(M_{d_n}(C))`; after choosing matrix units on each `M_{d_n}(C)`, this is a norm matrix corona with coordinate sizes `d_n²`." | `Analysis.AdjointDefectEstimate.naturalizeCoordinates`, `card_adjoint_naturalizeCoordinates_model`, `printedAdjointParagraph` | CARRIED |
| 137 | 594–596 | "`g ↦ σ̃(g)` is an exact homomorphism `G → U(B)`." | `Analysis.AdjointDefectEstimate.printedAdjointParagraph` (asymptotic-multiplicativity form; corona exactness is its quotient) | CARRIED |
| 138 | 596–597 | "Its restriction to `L` therefore extends to a `*`-homomorphism `C*_max(L) → B`." | `Analysis.maximalGroupCStarLift`, `maximalGroupCStar_existsUnique_lift` | PARTIAL — the universal lift exists, but the transport route does not use it (see #124) |
| 139 | 597–598 | "Let `P ∈ B` be the image of the Kazhdan projection [AkemannWalter]." | `Sofic.UltraproductKazhdanProjection.KazhdanCompressionRep.proj`, `kt_08_kazhdan_projection` | PARTIAL / CITED (AkemannWalter) — a spectral projection of the orbit average, not the `C*_max` Kazhdan projection |
| 140 | 598–600 | "Under the natural representation of `B` on `K_ω`, its range is `Fix σ(L)`." | `Sofic.UltraproductKazhdanProjection.kt_08_act_proj_of_fixed`, `act_proj_of_act_avg`, `act_avg_of_act_rep` | CARRIED |
| 141 | 600–602 | "This representation of `B` need not be faithful; it is used only after the following projection identity has been proved inside `B`." | — | MISSING (methodological remark; nothing asserts the ordering constraint) |
| 142 | 602–605 | "`U = σ̃(u)` satisfies the hypothesis of `lem:kazhdan-projection-order`, and hence `U*PU ≤ P` inside `B`." | `Sofic.UltraproductKazhdanProjection.kt_09_one_sided_compression`, `kt_09_conjugate_mul_proj`, `kt_09_proj_mul_conjugate` | CARRIED |
| 143 | 606 | "The two projections are unitarily equivalent." | `Analysis.MurrayVonNeumannEquiv.of_isometry_conjugate` | CARRIED |
| 144 | 606–607 | "`lem:stable-finite` therefore gives `U*PU = P`." | `Sofic.UltraproductKazhdanTransport.kt_10_finiteness_reverses_conjugate`, `UltraproductAdjointModel.kt_10_conjugate_eq` | CARRIED |
| 145 | 607–608 | "Hence both `U` and `U*` preserve `Fix σ(L)`, so `Uξ` and `U*ξ` are fixed by `σ(L)`." | `Sofic.UltraproductAdjointModel.starModel`, `act_pi_iota_of_act_P`, `pi_mul_P` | CARRIED |
| 146 | 608–611 | "The two limits vanish along `ω`. Since this holds for every free ultrafilter, both sequences converge ordinarily." | `Sofic.UltraproductKazhdanTransport.tendsto_along_free_ultrafilters`, `tendsto_of_sqrt_le` | CARRIED |

## §3 `cor:defect-hs` (ll. 614–621) and its proof (ll. 623–639)

| # | tex line | Claim | Lean declaration | Status |
| --- | --- | --- | --- | --- |
| 147 | 614–620 | `L` with (T), `uLu^{-1} ≤ L`, `c ∈ C_G(L)` ⟹ `[ucu^{-1},ℓ] ∈ R_{∞→2}(G)`. | `manuscriptCompressionDefectHSInvisible` | CARRIED |
| 148 | 624–626 | "`(V_n(c))` asymptotically commutes with `V_n(L)` in operator norm and hence in normalized Hilbert–Schmidt norm." | `Sofic.KazhdanCompressionCore` field `comm_c` + `hsNormSq_le_mul_self_l2_opNorm` | CARRIED |
| 149 | 627–628 | "Theorem `thm:transport` shows that the same is true of `(V_n(u)V_n(c)V_n(u)*)`." | `Sofic.KazhdanAsymptoticCommutant.compressionSet_transport_both_printed` | CARRIED |
| 150 | 628–632 | "Asymptotic multiplicativity identifies this sequence in operator norm with `(V_n(ucu^{-1}))`; explicitly `‖V_n(u)V_n(c)V_n(u)* − V_n(ucu^{-1})‖ → 0`." | `Sofic.KazhdanCornerMatrices.map_inv_vanishing` + `transport_star_printed` | PARTIAL — the triple-conjugation defect estimate is internal to `transport_star_printed`; no standalone lemma states the displayed limit |
| 151 | 633–637 | "Therefore `‖V_n([ucu^{-1},ℓ]) − 1‖₂ → 0`." | `Sofic.KazhdanCompressionCore.compressionDefects_eq_one_in_hyperlinearHom` | CARRIED |
| 152 | 638 | "Intersecting over `(V_n)` proves the claim." | `mem_opToHSShadowResidual_iff`, `mem_opToHSShadowResidual_iff_forall_hsKernel` | CARRIED |

## §4 Opening paragraph (ll. 643–648)

| # | tex line | Claim | Lean declaration | Status |
| --- | --- | --- | --- | --- |
| 153 | 643–644 | "For a normal Kazhdan subgroup `K ⊴ G`, the image of its Kazhdan projection is central relative to every representation of `G`." | `Analysis.NormalKazhdanUltraproduct.nk_07_commute_proj`, `nk_07_conjugate_proj` | CARRIED |
| 154 | 644–646 | "Its complement is therefore a canonical invariant sector on which `K` has no fixed vectors." | `Analysis.NormalKazhdanUltraproduct.nk_07_commute_q`, `nk_06_q_ne_zero` | CARRIED |
| 155 | 646–647 | "The finite-dimensional coordinates of this corner carry their own normalized matrix traces." | `Analysis.PrintedCornerCompression.PrintedCornerData.cornerModel`, `Sofic.hsLengthSq` | PARTIAL — the corner models and a normalized trace on them exist; nothing states that these are the corner's *own* traces as opposed to restrictions |
| 156 | 647–648 | "This is the sector on which the Kazhdan inequality detects every nontrivial corona image of `K`." | `Sofic.InternalRadicalGap` moving-corner machinery + `not_isWeakMF_of_normalKazhdan_le_defect` | PARTIAL — detection is proved on the moving corner, not via the printed corner Kazhdan inequality |

## §4 `lem:central-corona-corner` (ll. 650–660) and its proof (ll. 662–681)

| # | tex line | Claim | Lean declaration | Status |
| --- | --- | --- | --- | --- |
| 157 | 650–659 | Statement: a nonzero central projection yields, on an infinite coordinate subsequence, nonzero `q_n` and an operator-norm asymptotic representation `W_n : G → U(q_n M_{d_n}(C) q_n)` whose corona class is `g ↦ qρ(g)`. | `manuscriptCentralCoronaCorner` | CARRIED |
| 158 | 663 | "Lift `q` to projections `q_n`." | `Analysis.CollapseNormalizedSetup.exists_projection_lift_and_ultrafilter` | CARRIED |
| 159 | 663–664 | "and lift each `ρ(g)` to unitaries `U_n(g)`" | `Analysis.CollapseUnitaryLift.liftFam`, `unitarySequenceToCorona_liftFam` | CARRIED |
| 160 | 664 | "Projection lifting follows by spectral rounding." | `Analysis.CollapseProjectionLift.roundSeq`, `isOrthogonalProjectionMatrix_roundSeq`, `norm_spectralAbove_sub_le` | CARRIED |
| 161 | 664–666 | "Unitary lifting follows by polar-correcting any lift, since its two unitarity defects converge to zero in operator norm." | `Analysis.PolarLiftingGeneralCStar.polarUnitary`, `norm_polarUnitary_sub_le`; `CollapseUnitaryLift.liftFam` | CARRIED |
| 162 | 666–671 | Display: `‖q_nU_n(g) − U_n(g)q_n‖ → 0`. | `hcommOmega` step of `manuscriptCentralCoronaCorner`; `Analysis.PrintedCornerRelabelling.commutator_coord` | CARRIED |
| 163 | 672–673 | "`q_nU_n(g)q_n`, viewed on `q_n C^{d_n}`, has both unitarity defects converging to zero." | `Sofic.KazhdanCornerPolar.cornerGram`; `Analysis.NormMatrixCoronaUnitary` corner-Gram bound | CARRIED |
| 164 | 673–677 | "Its polar correction `W_n(g)` is unitary and `‖W_n(g) − q_nU_n(g)q_n‖ → 0`." | `Analysis.PrintedCornerCompression.PrintedCornerData.cornerMap_sub_compress_tendsto` | CARRIED |
| 165 | 678–679 | "The homomorphism relation for `ρ` now makes `(W_n)` an operator-norm asymptotic representation." | `Analysis.PrintedCornerCompression.PrintedCornerData.cornerRepresentation` | CARRIED |
| 166 | 679–680 | "Since `q ≠ 0`, infinitely many `q_n` are nonzero; retain those coordinates." | `Analysis.PrintedCornerRelabelling.exists_relabelling`; `PrintedCornerData.cornerModel_card_pos` | CARRIED |

## §4 `thm:normal-kazhdan` (ll. 683–689) and its proof (ll. 691–750)

| # | tex line | Claim | Lean declaration | Status |
| --- | --- | --- | --- | --- |
| 167 | 683–688 | `D ≤ R_{∞→2}(G)`, `K ⊴ G` with (T), `K ≤ D` ⟹ `K ≤ Rad_MF(G)`. | `manuscriptNormalKazhdanRadical`; `manuscriptNormalKazhdanPrintedRadical` | CARRIED |
| 168 | 692–695 | "Replace `G` by `Θ(G)`, replace `K` by `Θ(K)`, and denote the resulting inclusion into the corona again by `Θ`." | `Sofic.CoronaImageNormalKazhdan.nk_01_surviving_corona_representation`, `nk_02_countable_mf_image` | CARRIED |
| 169 | 695–696 | "The new `K` is a nontrivial normal property-(T) subgroup." | — | PARTIAL — normality and nontriviality are routine; nothing states that property (T) passes to `Θ(K)` in this step (`HasKazhdanPropertyT.of_mulEquiv` covers only the isomorphic case) |
| 170 | 696–700 | "Every one of its elements remains in the universal Hilbert–Schmidt kernel, because any operator-norm asymptotic representation of `Θ(G)`, precomposed with the quotient map from the original group, is such a representation of the original group." | `Sofic.map_opToHSShadowResidual_le` | CARRIED |
| 171 | 702–704 | "Let `p_K ∈ C*_max(K)` be the Kazhdan projection and `p` its image in `Q_d`. Thus `p` is the projection onto the `K`-fixed vectors in every faithful representation of the corona." | `Sofic.UltraproductKazhdanProjection.KazhdanCompressionRep.proj`, `kt_08_kazhdan_projection` | PARTIAL — spectral projection in the target algebra; no `C*_max(K)` Kazhdan projection and no "in every faithful representation" statement |
| 172 | 705–709 | Display: `Θ(g)pΘ(g)* = p` for `g ∈ G`. | `Analysis.NormalKazhdanUltraproduct.nk_07_conjugate_proj`, `nk_07_commute_proj` | CARRIED |
| 173 | 710–712 | "Indeed, in a faithful representation of the corona the two projections have ranges `Θ(g)Fix Θ(K)` and `Fix Θ(K)`; these agree because `gKg^{-1}=K`." | — | MISSING (proof-internal; `nk_07_conjugate_proj` is proved algebraically, not through ranges in a faithful representation) |
| 174 | 713–714 | "Put `q = 1 − p`. The projection `q` is nonzero, since `p=1` would imply that every element of `K` has trivial image." | `Analysis.NormalKazhdanUltraproduct.nk_06_q_ne_zero`, `nk_06_rep_eq_one_of_q_eq_zero` | CARRIED |
| 175 | 714–716 | "`lem:central-corona-corner` gives an operator-norm asymptotic representation `(W_n)` on nonzero corners." | `manuscriptCentralCoronaCorner` | CARRIED |
| 176 | 718–719 | "Choose a finite symmetric Kazhdan set `S ⊆ K` and a Kazhdan constant `κ > 0`." | `Kazhdan.KazhdanProjection.HasKazhdanPropertyT.exists_symmetric_generating_pair` | CARRIED |
| 177 | 719–720 | "In the corner `qQ_dq`, the Kazhdan projection is zero." | — | MISSING (proof-internal; load-bearing for the printed route) |
| 178 | 720–728 | Display: `b = (1/\|S\|)Σ_{s∈S}(qΘ(s)q − q)*(qΘ(s)q − q)` satisfies `b ≥ (κ²/\|S\|)q`. | — | MISSING (proof-internal; load-bearing for the printed route) |
| 179 | 729–730 | "Indeed, in every representation of the corner there are no `K`-fixed vectors, so the defining Kazhdan inequality gives this operator inequality." | — | MISSING (proof-internal) |
| 180 | 732–741 | "The coordinate elements `b_n = (1/\|S\|)Σ(W_n(s) − q_n)*(W_n(s) − q_n)` represent `b`. Taking the normalized trace on `q_nM_{d_n}(C)q_n` yields `(1/\|S\|)Σ‖W_n(s) − q_n‖₂² ≥ κ²/\|S\| − o(1)`." | — | MISSING (proof-internal) |
| 181 | 742–745 | "The order inequality for `b` says that the negative part of `b_n − (κ²/\|S\|)q_n` converges to zero in operator norm, which gives the displayed trace inequality." | — | MISSING (proof-internal) |
| 182 | 746–748 | "After passing to a subsequence, one fixed `s_0 ∈ S` therefore stays a positive Hilbert–Schmidt distance from the corner identity." | `Sofic.InternalRadicalGap.ambientMovingCompression_*`, `not_isWeakMF_of_normalKazhdan_le_defect` | PARTIAL — the Lean contradiction is the moving-corner separation, not the printed corner-trace one |
| 183 | 748–749 | "This contradicts `s_0 ∈ K ≤ D ≤ R_{∞→2}(G)`. Thus every corona homomorphism kills `K`." | `manuscriptNormalKazhdanCoronaVanishing` | CARRIED |

## §4 Proof of Theorem A (ll. 752–770)

| # | tex line | Claim | Lean declaration | Status |
| --- | --- | --- | --- | --- |
| 184 | 753–757 | "For every `u ∈ Comp_G(L)`, `c ∈ C_G(L)`, `ℓ ∈ L`, `cor:defect-hs` gives `[ucu^{-1},ℓ] ∈ R_{∞→2}(G)`." | `manuscriptCompressionDefectHSInvisible` | CARRIED |
| 185 | 758–761 | "Normality of `R_{∞→2}(G)` therefore gives `𝔇_G(L) ≤ R_{∞→2}(G)`." | `printedDefect_le_opToHSShadowResidual_direct`; `manuscriptPrintedDefectShadowInclusion`; `manuscriptShadowResidualCoversNormalClosure` | CARRIED |
| 186 | 762–764 | "`thm:normal-kazhdan` now gives `K ≤ Rad_MF(G)`. The two stated consequences follow by taking `K≠1`, or `K=G=𝔇_G(L)`." | `manuscriptPrintedCriterionAssembly`; `manuscriptPrintedDefectNormalKazhdanRadical` | CARRIED |
| 187 | 766–769 | "For a finite-dimensional linear representation over an arbitrary field, `thm:commutant` kills every generator of `𝔇_G(L)`. Its kernel is normal, so it contains `𝔇_G(L)`." | `manuscriptPrintedDefectFiniteDimensionalSterility` (`printedDefect_le_compressionCentralizerDefect` then `compressionCentralizerDefect_le_ker`) | CARRIED |

## §4 `prop:defect-saturation` (ll. 772–794) and its proof (ll. 796–813)

| # | tex line | Claim | Lean declaration | Status |
| --- | --- | --- | --- | --- |
| 188 | 775–778 | `eq:defect-functoriality`: `f(D) ≤ 𝔇_{f(G)}(f(L))`. | `map_printedDefect_to_range_le`; `manuscriptDefectSaturation` cl. 1 | CARRIED |
| 189 | 779–780 | "If `S ≤ G` is a nontrivial simple subgroup and `D ∩ S ≠ 1`, then `S ≤ D`." | `simple_le_printedDefect_of_inf_ne_bot` | CARRIED |
| 190 | 780–781 | "If in addition the normal closure of `S` in `G` is all of `G`, then `D=G`." | `printedDefect_eq_top_of_simple_normalClosure_eq_top` | CARRIED |
| 191 | 783–786 | "`f` onto, `S ≤ D` simple, `f(S)≠1`, `f(S)` normally generates `Q` ⟹ `𝔇_Q(f(L))=Q`." | `printedDefect_map_eq_top_of_simple_image_normalClosure_eq_top` | CARRIED |
| 192 | 789–792 | "Consequently, if `L` and `G` have property (T), these hypotheses imply `Rad_MF(G)=G`." | `manuscriptCoronaMFResidual_eq_top_of_printedDefect_saturation`; `manuscriptDefectSaturation` cl. 5 | CARRIED |
| 193 | 797–798 | "If `u ∈ Comp_G(L)`, then `f(u)f(L)f(u)^{-1} ≤ f(L)`." | `map_mem_printedCompressionSet` | CARRIED |
| 194 | 798–799 | "if `c ∈ C_G(L)`, then `f(c) ∈ C_{f(G)}(f(L))`" | inside `map_printedDefect_le` | CARRIED |
| 195 | 799–801 | "Therefore `f` takes every defining generator of `D` into a defining generator of `𝔇_{f(G)}(f(L))`." | `map_printedDefect_le` | CARRIED |
| 196 | 803–804 | "The subgroup `D` is normal in `G`, so `D ∩ S` is normal in `S`." | `printedDefect_normal` (instance) + mathlib `Subgroup.normal_inf` | CARRIED |
| 197 | 804 | "Simplicity and `D ∩ S ≠ 1` give `D ∩ S = S`, hence `S ≤ D`." | `simple_le_printedDefect_of_inf_ne_bot` | CARRIED |
| 198 | 804–806 | "Since `D` is normal in `G`, it then contains the normal closure of `S`. Under the second hypothesis this is `G`." | `printedDefect_eq_top_of_simple_normalClosure_eq_top` | CARRIED |
| 199 | 808–810 | "`f(S) ≤ 𝔇_Q(f(L))`. The latter subgroup is normal in `Q`, so it contains the normal closure of `f(S)` and is therefore all of `Q`." | `printedDefect_map_eq_top_of_simple_image_normalClosure_eq_top` | CARRIED |
| 200 | 810–812 | "The last assertion is `thm:compression-criterion` with `K=G`." | `manuscriptOneSidedCompressionCriterion` cl. 3 | CARRIED |

## §5 The binary Leavitt self-compression (ll. 824–898)

| # | tex line | Claim | Lean declaration | Status |
| --- | --- | --- | --- | --- |
| 201 | 826–829 | "`R = L_{F2}(1,2)` and `p = s_0t_0`, `q = s_1t_1`." | `RTE.R`, `RTE.q`; `LeavittFamily.p0`, `LeavittFamily.p1` | CARRIED |
| 202 | 830–833 | `eq:pq` first half: `p + q = 1`. | `LeavittFamily.p0_add_p1` | CARRIED |
| 203 | 830–833 | `eq:pq` second half: `t_1 q s_1 = 1`. | `LeavittFamily.t1_mul_p1_mul_s1` | CARRIED |
| 204 | 834 | "In particular `q ≠ 0`." | `RTE.q_ne_zero`; `LeavittFamily.p1_ne_zero` | CARRIED |
| 205 | 836–839 | "We use indices `0,…,11`, and identify `GL_3(R)` with the matrices `diag(A,I_9)` in `GL_12(R)`." | `RankTwelve.fullCorner`, `RankTwelve.halfCorner`; `RTE.frame12`, `RTE.flat12`, `RTE.cornerIndex` | CARRIED |
| 206 | 838–842 | `eq:matrix-compression`: `Ψ(A) = qI_3 + s_0At_0`, "the unital injective endomorphism". | `LeavittFamily.matrixCompression` | CARRIED |
| 207 | 843 | "Here `s_0At_0` denotes the matrix `(s_0a_{ij}t_0)_{ij}`." | `LeavittFamily.matrixCompression_apply` | CARRIED |
| 208 | 843–845 | "The relations `qs_0 = t_0q = 0` and `t_0s_0 = 1` show that `Ψ` is multiplicative and unital." | `LeavittFamily.p1_mul_s0`, `t0_mul_p1`, `t0_s0`; `PrintedLeavittEquations.printed_q_mul_s0`, `printed_t0_mul_q`; `matrixCompression_mul`, `matrixCompression_one` | CARRIED |
| 209 | 845 | "The identity `t_0Ψ(A)s_0 = A` proves injectivity." | `LeavittFamily.matrixCompression_recover`, `matrixCompressionHom_injective`; `PrintedLeavittEquations.printed_matrixCompression_injective` | CARRIED |
| 210 | 845–846 | "The term `qI_3` is needed for unitality because the map `A ↦ s_0At_0` sends `I_3` to `pI_3`." | `PrintedLeavittEquations.printed_scalarDiagonal_image_of_one`, `printed_p0_ne_one`, `printed_scalarDiagonal_p0_ne_one`; `matrixCompression_one` | CARRIED |
| 211 | 848–853 | Display: `X` and `Y` as `2×2` block matrices over `M_3(R)`. | `RankTwelve.shift`, `RankTwelve.shiftInv` | CARRIED |
| 212 | 854 | "A direct calculation using `eq:leavitt` gives `XY = YX = I_6`." | `RankTwelve.shift_mul_shiftInv`, `RankTwelve.shiftInv_mul_shift` | CARRIED |
| 213 | 855–857 | `eq:tau`: `τ = diag(X,Y) ∈ GL_12(R)`. | `RankTwelve.tau`, `RankTwelve.tauUnit`; `RTE.printedTauGL` | CARRIED |
| 214 | 858–867 | `eq:whitehead-factorization`: the six-factor Whitehead product for `diag(X,X^{-1})`. | `RankTwelve.tau_eq_whitehead_product`; `RTE.tauUnit_eq_six_elementary` | CARRIED |
| 215 | 868–870 | "Each block-unipotent factor is a product of elementary `12×12` matrices: its off-diagonal `6×6` block may be inserted one entry at a time, and the corresponding matrix units have pairwise zero products." | `RTE.flat12Units_elementary_single_mem`, `RTE.flat12Units_elementary_mem`, `RTE.flat12_single` | CARRIED |
| 216 | 871–872 | "Since `Y = X^{-1}`, the factorization proves `τ ∈ EL_12(R)`." | `RTE.printedTauGL_mem`, `RTE.printedTauGL_eq_flat12Units` | CARRIED |
| 217 | 874–880 | "Let `H = EL_12(R)` and let `L = EL_3(R) ≤ H` be the upper-left corner." | `RTE.H`, `RTE.corner`, `RTE.cornerRootSet` | CARRIED |
| 218 | 881–882 | "Both groups have property (T) by the theorem of Ershov and Jaikin-Zapirain." | `RTE.hasKazhdanPropertyT`, `RTE.corner_hasKazhdanPropertyT` | CARRIED — but see #96 for the more general cited theorem |
| 219 | 883–887 | `eq:corner-conjugation`: `τ diag(A,I_9) τ^{-1} = diag(Ψ(A), I_9)`. | `RankTwelve.tau_fullCorner_tauInv`, `RankTwelve.shift_halfCorner_shiftInv` | CARRIED |
| 220 | 888–889 | "For every `i≠j` and `a ∈ R`, `Ψ(e_ij(a)) = e_ij(s_0at_0)`." | `LeavittFamily.matrixCompression_elementaryUnit` | CARRIED |
| 221 | 890–892 | `eq:compresses-L`: `τLτ^{-1} ≤ L`. | `RTE.tau_compresses_corner`, `RTE.tau_conj_corner_elementaryRoot`; `PrintedLeavittEquations.printed_tau_conj_corner_subset` | CARRIED |
| 222 | 894–895 | "The field `F_2` is used in the diagonal branch: the only central unit of `R` is `1`." | `BinaryLeavitt.central_units_trivial` | CARRIED |
| 223 | 895–897 | "The dimension 12 comes from applying the `6×6` Whitehead factorization to the `3×3` Kazhdan corner." | `RTE.corner_hasKazhdanPropertyT`; `RTE.tauUnit_eq_six_elementary` | PARTIAL — both construction components are formalized, but this explanatory provenance is not a named assertion |
| 224 | 897–898 | "We do not claim that 12 is minimal." | — | MISSING (disclaimer; nothing to formalize) |

## §6 `prop:simple` and its direct proof (ll. 902–1020)

| # | tex line | Claim | Lean declaration | Status |
| --- | --- | --- | --- | --- |
| 225 | 902–904 | "The group `H = EL_12(R)` is simple." | `RTE.normalRootDetection`; `RTE.manuscriptPropositionSimple` | CARRIED |
| 226 | 907–911 | `eq:two-sided-sandwich`: every `0 ≠ x ∈ R` admits `a,b` with `axb=1`. | `BinaryLeavitt.exists_mul_mul_eq_one`; `BinaryLeavitt.hasSingleSandwichDivision`; `RTE.coefficientRing_hasSingleSandwichDivision` | CARRIED |
| 227 | 912 | "This is the form of pure infiniteness needed here." | `HasSingleSandwichDivision`; `BinaryLeavitt.hasSingleSandwichDivision` | PARTIAL / CITED (AbramsAranda) — the exact operative property is proved; no general pure-infiniteness predicate is introduced |
| 228 | 913–915 | "The only central unit of `R` is `1`, because `Z(R)=F_2` and `F_2^×={1}`." | `BinaryLeavitt.center_eq_bot`, `eq_smul_one_of_central`, `central_units_trivial`; `PrintedLeavittEquations.printed_f2_units_subsingleton` | CARRIED |
| 229 | 917–920, 935–937 | "A normal subgroup containing a nonzero elementary root whose coefficient sandwiches to `1` is the whole elementary group; hence simplicity reduces to root detection." | `elementaryGroup_normal_eq_top_of_elGen_mem`; `normalClosure_elGen_eq_top`; `isSimpleGroup_of_rootDetection` | CARRIED |
| 230 | 920–926 | The two displayed commutators turn `e_ij(x)` and `axb=1` into a unit root. | `elGen_commutator`; `elGen_map_eq_one_of_left`, `elGen_map_eq_one_of_right`, `elGen_map_eq_one_of_unit_sandwich` | CARRIED |
| 231 | 926–934 | The two displayed source/target commutators move a unit root and attach an arbitrary coefficient `r`. | `elGen_commutator`; `elGen_map_eq_one_source_step`, `elGen_map_eq_one_target_step` | CARRIED |
| 232 | 933–935 | "Repeating these moves … gives every elementary generator." | `elGen_map_one_eq_one_all_pairs`, `elGen_map_eq_one_all`, `elementaryGroup_hom_eq_one_of_gens` | CARRIED |
| 233 | 939–943 | `eq:coefficient-separation`: for nonzero `r,s`, there are `a,b` with `arb=0` and `bsar≠0`. | `exists_annihilate_preserve_reverse` | CARRIED |
| 234 | 944–945 | "For every `w∈R` there are `x,y` with `xwy=0` and `yx≠0`." | `exists_reversing_zero_product` | CARRIED |
| 235 | 945 | "For `w=0`, take `x=y=1`." | inside `exists_reversing_zero_product` | PARTIAL — exact proof branch, not a separately named assertion |
| 236 | 946–947 | For `w≠0`, choose `c,d` with `cwd=1`, then put `x=t_1c`, `y=ds_0`; this gives `xwy=0`. | inside `exists_reversing_zero_product`; `LeavittFamily.t1_s0` | PARTIAL — exact witness calculation is internal to the named theorem |
| 237 | 947–950 | `s_0t_1≠0`, since `1=(t_0s_0)(t_1s_1)=t_0(s_0t_1)s_1`. | inside `exists_reversing_zero_product` | PARTIAL — the displayed contradiction is formalized inside the theorem, not separately named |
| 238 | 951–955 | If `yx=ds_0t_1c=0`, sandwiching it by `cw` and `wd` forces `s_0t_1=0`. | inside `exists_reversing_zero_product` | PARTIAL — proof-internal calculation |
| 239 | 956–964 | The four sandwich factorizations and the displayed definitions of `a,b` produce the coefficient-separation witnesses. | inside `exists_annihilate_preserve_reverse` | PARTIAL — exact witness construction is internal to the named theorem |
| 240 | 965–966 | `arb=0`, while `bsar=0` would imply `yx=0`. | `exists_annihilate_preserve_reverse` | CARRIED |
| 241 | 968 | For nontrivial normal `N`, choose `1≠g∈N`. | inside `rootDetection_of_leavittFamily`; `Subgroup.ne_bot_iff_exists_ne_one` | PARTIAL — proof-internal choice |
| 242 | 969–970 | The inverse of a diagonal invertible matrix is diagonal. | `matrixUnit_inv_offDiag_eq_zero` | CARRIED |
| 243 | 970–973 | If diagonal `g` commutes with every elementary root, it is a scalar central unit and hence `g=1`. | `ElementarySimplicity.center_elementaryGroup_eq_bot_of_units`; `exists_elGen_mem_of_diagonal` | CARRIED |
| 244 | 973–978 | Some elementary root is sent by conjugation to the same root line with a different coefficient, so its commutator with `g` is a nonzero root in `N`. | `conjSingle_eq_single_of_concentrated`; `exists_elGen_mem_of_conjSingle_eq`; `exists_elGen_mem_of_diagonal` | CARRIED |
| 245 | 980–981 | If `g` is not diagonal, choose `ℓ≠i` with `g_{ℓi}≠0` and put `r=(g⁻¹)_{ℓi}`. | inside `rootDetection_of_leavittFamily` | PARTIAL — exhaustive case selection is internal to the root-detection theorem |
| 246 | 981–989 | If `r=0`, the matrices `A=gE_{iℓ}g⁻¹`, `B=E_{iℓ}` satisfy `AB=0`, and the displayed double commutator is `1-BA∈N`. | `doubleCommutator_mem`, `doubleCommutator_eq_sqZeroUnit`; `exists_elGen_mem_of_inv_entry_zero` | CARRIED |
| 247 | 989–994 | The sparse defect `-BA` is square-zero, row-supported, and has a nonzero entry in that row. | `neg_mul_sq_eq_zero_of_left_annihilates`, `isRowSupported_single_mul`, `exists_mul_inv_entry_ne_zero`; `exists_elGen_mem_of_inv_entry_zero` | CARRIED |
| 248 | 996–1001 | If `r≠0`, coefficient separation supplies `a,b` with `arb=0`, `bsar≠0`, and defines the dense-case `A,B`. | `exists_annihilate_preserve_reverse`; `exists_elGen_mem_of_dense_entries` | CARRIED |
| 249 | 1002–1006 | In the dense case `AB=0`; the commuting elementary roots and reduction modulo `N` give the displayed double commutator `1-BA∈N`. | `elGen_commute`, `doubleCommutator_mem`, `doubleCommutator_eq_sqZeroUnit`; `exists_elGen_mem_of_annihilating_coefficients` | CARRIED |
| 250 | 1007–1008 | The dense defect is square-zero and row-supported, with `(i,i)` entry `-bsar≠0`. | `neg_mul_sq_eq_zero_of_left_annihilates`, `isRowSupported_single_mul`; `exists_elGen_mem_of_annihilating_coefficients` | CARRIED |
| 251 | 1010–1016 | A row-supported square-zero unipotent with nonzero `v_im` yields the displayed row-extraction commutator `e_in(v_im)∈N`. | `row_supported_commutator_of_sq_zero`; `exists_elGen_mem_of_row_supported_sq_zero` | CARRIED |
| 252 | 1017–1018 | The extracted nonzero root normally generates, so `N=H`; every normal subgroup is trivial or all of `H`. | `elementaryGroup_normal_eq_top_of_elGen_mem`; `rootDetection_of_leavittFamily`; `isSimpleGroup_of_leavittFamily_root_extraction` | CARRIED |
| 253 | 1019 | `e_01(1)≠1`, so `H` is nontrivial. | `RTE.elementaryRoot_eq_one_iff`; `RTE.nontrivial` | CARRIED |

## §6 `prop:defect` (ll. 1022–1063)

| # | tex line | Claim | Lean declaration | Status |
| --- | --- | --- | --- | --- |
| 254 | 1022–1028 | "`c = e_34(1)`, `ℓ = e_12(1)`, `d = [τcτ^{-1}, ℓ]` in `H`." | `RTE.c`, `RTE.ell`, `RTE.defect`, `RTE.tau` | CARRIED |
| 255 | 1043–1046 | Display: `c ∈ C_H(L)`, `d = e_02(q) ≠ 1`, `⟨⟨d⟩⟩_H = H`. | `RTE.PropositionDefect`; `RTE.manuscriptPropositionDefect` | CARRIED |
| 256 | 1049–1052 | The upper-left generators commute with `c=e_34(1)`, so `c∈C_H(L)`. | `RTE.c_commutes_corner` | CARRIED |
| 257 | 1054–1057 | `eq:moved-mark`: `τcτ^{-1}=e_01(q)e_34(1)`. | `RTE.tau_conj_c`, `RTE.tau_conj_rawC`, `RTE.flat12_rawMovedC` | CARRIED |
| 258 | 1058–1060 | The second factor commutes with `ℓ`, and the elementary commutator relation gives `d=e_02(q)`. | `Leavitt.elementaryRoot_commutator`; `RTE.tau_c_commutator_ell` | CARRIED |
| 259 | 1060 | `d` is nontrivial because `q≠0`. | `RTE.defect_ne_one` | CARRIED |
| 260 | 1060–1062 | Since `t_1qs_1=1`, the sandwiched-root argument gives `⟨⟨d⟩⟩_H=H` directly. | `normalClosure_elementaryRoot_eq_top_of_unit_sandwich`; `RTE.normalClosure_defect_eq_top` | CARRIED |

## §6 Proof of Theorem B (ll. 1065–1085)

| # | tex line | Claim | Lean declaration | Status |
| --- | --- | --- | --- | --- |
| 261 | 1066 | "The finitely generated `F_2`-algebra `R` is countable, and hence so is `H`." | the `Countable (BinaryLeavittAlgebra k)` instance in `UniversalLeavittOver`; `RTE.countable` | CARRIED |
| 262 | 1067–1069 | "The ring `R` is finitely generated, and `H` has property (T)." | the `Algebra.FiniteType k (BinaryLeavittAlgebra k)` instance in `UniversalLeavittOver`; `RTE.hasKazhdanPropertyT` | CARRIED |
| 263 | 1071–1073 | Compression, centrality of `c`, and `prop:defect` give `d∈𝔇_H(L)`. | `RTE.printedDefectConfiguration`; `printedDefect_generator_mem` | CARRIED |
| 264 | 1073–1075 | Normality of `𝔇_H(L)` and `⟨⟨d⟩⟩_H=H` give `𝔇_H(L)=H`. | `RTE.printedDefect_eq_top_of_configuration` | CARRIED |
| 265 | 1075–1077 | The compression criterion with `K=H` gives `Rad_MF(H)=H`. | `RTE.residual_eq_top_of_configuration`; `RTE.rankTwelve_actualCoronaMFResidual_eq_top` | CARRIED |
| 266 | 1078–1079 | Independently, `prop:simple` shows that `H` is nontrivial and simple. | `RTE.nontrivial`; `RTE.manuscriptPropositionSimple` | CARRIED |
| 267 | 1081–1084 | Every homomorphism from `H` to an MF group is trivial. | `manuscriptFullRadicalKillsMFTargets`; `manuscriptBinaryLeavittHeadline` | CARRIED |
| 268 | 1083–1084 | If `H` were MF, its identity homomorphism would contradict the preceding conclusion. | `Sofic.not_isCDEOperatorMF_of_actualCoronaMFResidual_eq_top`; `RTE.not_isCDEOperatorMF_of_residual_eq_top` | CARRIED |

## §7 Prescribed MF quotients (ll. 1087–1134)

| # | tex line | Claim | Lean declaration | Status |
| --- | --- | --- | --- | --- |
| 269 | 1089–1090 | "`B` countable with `Rad_MF(B)=B`, `1≠d∈B` normally generating `B`; put `A=⟨d⟩`." | `MFCamouflage.Edge`, `MFCamouflage.edgeIsCyclic`, `MFCamouflage.edgeGenerator` | CARRIED |
| 270 | 1118–1121 | `eq:amalgam`: `W_Q=B*_A(Q×A)`, with `A` included in the second factor. | `MFCamouflage.Camouflage`, `MFCamouflage.leftEdge`, `MFCamouflage.rightEdge` | CARRIED |
| 271 | 1121–1123 | The trivial map from `B` and projection `Q×A→Q` agree on `A`. | `MFCamouflage.projectionFamily`, `projection` | CARRIED |
| 272 | 1123–1131 | They define an epimorphism `π_Q:W_Q→Q`. | `MFCamouflage.projection`, `projection_surjective` | CARRIED |
| 273 | 1132 | It is split by `Q→Q×A→W_Q`. | `MFCamouflage.visible`, `projection_comp_visible`; `SplitPrescribedProjection` cl. 4 | CARRIED |
| 274 | 1132–1134 | Both vertex maps are injective by the amalgam normal-form theorem. | `MFCamouflage.blackHole_injective`, `productVertex_injective` | CARRIED |
| 275 | 1134 | In particular, `d≠1` in `W_Q`. | `MFCamouflage.defect_ne_one` | CARRIED |

## §7 `prop:universal-factorization` and its proof (ll. 1136–1175)

| # | tex line | Claim | Lean declaration | Status |
| --- | --- | --- | --- | --- |
| 276 | 1136–1147 | Maps `B→T` all trivial imply precomposition with `π_Q` bijects `Hom(Q,T)` with `Hom(W_Q,T)`. | `manuscriptUniversalFactorization` cl. 1; `MFCamouflage.precomp_bijective` | CARRIED |
| 277 | 1148–1156 | `ker π_Q=⟨⟨d⟩⟩_{W_Q}`. | `manuscriptUniversalFactorization` cl. 2; `MFCamouflage.projection_ker_eq_normalClosure` | CARRIED |
| 278 | 1160–1161 | The restriction to `B`, hence to the amalgamated `A`, is trivial. | inside `MFCamouflage.factor_through_projection` | PARTIAL — no separately named step |
| 279 | 1162–1165 | `f(q,a)=f(q,1)f(1,a)=f(q,1)`. | `MFCamouflage.productVertex_eq_visible_mul_blackHole`, `product_edge_eq_blackHole` | CARRIED |
| 280 | 1166–1167 | The restriction to `Q×A` factors uniquely through projection to `Q`. | `MFCamouflage.factor_through_projection` | CARRIED |
| 281 | 1167–1168 | The amalgam universal property makes `f` factor through `π_Q`. | `MFCamouflage.factor_through_projection` | CARRIED |
| 282 | 1168–1169 | Uniqueness follows from surjectivity of `π_Q`. | `projection_surjective`; injectivity half of `precomp_bijective` | CARRIED |
| 283 | 1171 | `d∈ker π_Q`. | `MFCamouflage.projection_blackHole` | CARRIED |
| 284 | 1171–1174 | Quotienting by `⟨⟨d⟩⟩` kills `B` and the second factor `A`, leaving `Q`. | `MFCamouflage.projection_ker_eq_normalClosure` | CARRIED |

## §7 Proof of Theorem C (ll. 1177–1198)

| # | tex line | Claim | Lean declaration | Status |
| --- | --- | --- | --- | --- |
| 285 | 1178–1180 | Every homomorphism from `B` to an MF group is trivial. | `MFCamouflage.actualCoronaHom_eq_one_of_residual_eq_top`; `manuscriptFullRadicalKillsMFTargets` | CARRIED |
| 286 | 1180–1181 | Universal factorization gives the bijection for every MF target. | `MFCamouflage.cdeMF_precomp_bijective` | CARRIED |
| 287 | 1182–1186 | Every corona homomorphism from `W_Q` factors uniquely through `π_Q`. | `MFCamouflage.actualCorona_precomp_bijective` | CARRIED |
| 288 | 1186–1190 | Intersecting kernels gives `Rad_MF(W_Q)=π_Q⁻¹(Rad_MF(Q))`. | `MFCamouflage.actualCoronaMFResidual_eq_comap` | CARRIED |
| 289 | 1191–1192 | The radical contains `ker π_Q` and its nonidentity `d`, so `W_Q` is non-MF. | `MFCamouflage.projection_ker_le_actualCoronaMFResidual`; `manuscriptPrescribedMFQuotients` cl. 3 | CARRIED |
| 290 | 1192–1196 | If `Q` is MF, `Rad_MF(W_Q)=ker π_Q=⟨⟨d⟩⟩_{W_Q}`. | `MFCamouflage.actualCoronaMFResidual_eq_ker`, `MFCamouflage.projection_ker_eq_normalClosure` | CARRIED |

## §7 Closing relation calculus (ll. 1200–1219)

| # | tex line | Claim | Lean declaration | Status |
| --- | --- | --- | --- | --- |
| 291 | 1200–1206 | `eq:closure-pullback`: `cl_MF^{W_Q}(N)=π_Q⁻¹(cl_MF^Q(π_Q(N)))`. | `MFCamouflage.actualCoronaMFClosure_eq_comap`; `manuscriptPrescribedQuotientRelationCalculus` cl. 1 | CARRIED |
| 292 | 1207–1208 | An MF-target map from `W_Q` kills `N` iff its unique factor through `Q` kills `π_Q(N)`. | `ClosurePullback.factorsMFTargets_iff_ker_le`, `literalMFClosure_eq_comap_of_factors`, `manuscriptMFClosurePullbackAlongFactorization` | CARRIED |
| 293 | 1208–1216 | `W_Q/N` is MF iff `ker π_Q≤N` and `Q/π_Q(N)` is MF. | `MFCamouflage.quotient_isCDEOperatorMF_iff`; `manuscriptPrescribedQuotientRelationCalculus` cl. 2 | CARRIED |
| 294 | 1217–1219 | If `ker π_Q≤N`, then `N=π_Q⁻¹(π_Q(N))`. | `manuscriptPrescribedQuotientRelationCalculus` cl. 3 | CARRIED |

---

# MISSING, ranked by how much the printed proof leans on it

There is no missing numbered statement: the strict claim count is 15/15.
In particular, `RTE.normalRootDetection` and
`RTE.manuscriptPropositionSimple` close the rank-twelve simplicity endpoint by
direct root extraction.  The rows below are proof-internal assertions whose
enclosing theorems are carried by different formal routes.

## Tier 1 — load-bearing for the *printed proof route* of `thm:normal-kazhdan`

The theorem itself (#167) is closed, but by the moving-corner/`WeakMF` route.
The printed §4 proof — the one a referee will read — turns on five sentences
with no declaration.  A reader checking the paper against the Lean cannot verify
them.

1. **#177 — "In the corner `qQ_dq`, the Kazhdan projection is zero."**  Needed:
   `theorem : (KazhdanCompressionRep.proj D) * (1 - p) = 0` in the corner
   algebra, i.e. the image of the Kazhdan projection under the corner
   compression vanishes.
2. **#178 / #179 — the corner Kazhdan inequality
    `b = (1/|S|)Σ(qΘ(s)q − q)*(qΘ(s)q − q) ≥ (κ²/|S|)q`.**  Needed:
    `theorem corner_kazhdan_lower_bound (D : KazhdanCompressionRep …) (S : Finset K) (kappa : ℝ) (h : IsKazhdanPair K S kappa) (hq : q * proj = 0) : (κ^2 / S.card) • q ≤ (1/S.card) • ∑ s ∈ S, star (q * Θ s * q - q) * (q * Θ s * q - q)`
    (with the order relation spelled as absorption, as in
    `manuscriptNormMatrixCoronaStableFinite`).
3. **#180 / #181 — the trace consequence.**  Needed:
    `theorem : Filter.liminf (fun n ↦ (1/S.card) * ∑ s ∈ S, hsLengthSq (cornerModel n) (W n s - q n)) atTop ≥ κ^2 / S.card`,
    derived from 10 via "the negative part of `b_n − (κ²/|S|)q_n` tends to zero
    in operator norm" — which itself needs a named lemma
    `theorem negPart_tendsto_zero_of_corona_le`.
4. **#129 — "Faithfulness of the representation gives the same projection
    inequality in `B`."**  This is the one place `lem:kazhdan-projection-order`
    as *printed* is not closed: `Analysis/KazhdanProjectionOneSidedOrder.lean`
    proves the Hilbert-space half and leaves the `C*`-algebra bridge as a
    hypothesis; `manuscriptOneSidedKazhdanProjectionOrder` sidesteps it entirely
    by rebuilding `P` spectrally in `B`.  Needed:
    `theorem le_of_le_in_faithful_rep {B} [CStarAlgebra B] (π : B →⋆ₐ[ℂ] (H →L[ℂ] H)) (hπ : Function.Injective π) {p q : B} (hp : IsStarProjection p) (hq : IsStarProjection q) : π q ≤ π p → q * p = q`.

## Tier 2 — proof-internal to a `CARRIED` theorem; the paper does not lean on them

5. #35, #36, #31 — the diagonal-sum construction inside the proof of
    `prop:mf-residual-calculus` (defects `≤ 1/n`, half separation retained, the
    quotient norm as a limsup, the enumeration).  `G/R` is MF is closed by an
    ultraproduct route.
6. #173 — "in a faithful representation the two ranges agree because
    `gKg^{-1}=K`"; `nk_07_conjugate_proj` is algebraic.
7. #141 — "this representation of `B` need not be faithful; it is used only
    after the projection identity has been proved inside `B`".
8. #224 — "We do not claim that 12 is minimal" (disclaimer).

## Historical Preusser route — optional development only

The current manuscript mentions Preusser's general normal-subgroup theorems
only as historical context in #95 and immediately says that the proof instead
extracts a root directly.  `rootDetection_of_leavittFamily` proves the required
root detection.  The repository additionally retains an optional development
around the stronger Preusser sandwich:

* `relativeElementary` and `congruenceSubgroup` are the printed `EL_n(R,I)` and
  `C_n(R,I)`;
* `normalLevel` and `relativeElementary_normalLevel_le` give a canonical level
  and its lower inclusion;
* `relativeElementary_top`, `congruenceSubgroup_bot`,
  `exists_central_scalar_of_mem_center`, and
  `center_eq_bot_of_central_units_trivial` prove the two case-split endpoints;
  and
* `isSimpleGroup_of_preusser_sandwich` packages the complete implication from
  the one remaining cited upper-sandwich hypothesis to simplicity.

The exchange prerequisite and coefficient-ring inputs are also internal:
`BinaryLeavitt.hasRightExchange`,
`BinaryLeavitt.hasSingleSandwichDivision`,
`HasSingleSandwichDivision.isSimpleRing`, `BinaryLeavitt.center_eq_bot`, and
`BinaryLeavitt.central_units_trivial`.

*#105 and #78 were on this list until `PrintedRemarks.lean` landed mid-sweep.*
`manuscriptCommutantFiniteDimensionalHypothesisIsEssential` now supplies the
explicit injective non-surjective `Φ` on `End_C(ℕ → C)`
(`shiftConjugation_not_surjective`), and
`manuscriptFullRadicalsDoNotEntailNonsoficity` now supplies the
soficity/hyperlinearity separation with a nontriviality guard.  Both are
`CARRIED`.

---

# CITED

Every literature dependence in the manuscript, with the exact claim and the
paper.  No citation is load-bearing for a numbered endpoint.  In particular,
the simplicity proof uses the internally proved sandwich, central-unit, and
direct root-extraction statements rather than Preusser's general theorem.

| # | tex line | Claim | Paper | In-repo status |
| --- | --- | --- | --- | --- |
| 16 | 127–129 | "*MF group* means this operator-norm notion." | Carrión–Dadarlat–Eckhardt (`CDE`); Korchagin (`Korchagin`) | Definition is formalized (`Sofic.IsCDEOperatorMF`); the citation is attribution only |
| 52 | 275–277 | "Whether every countable group is MF … remained open." | `CDE`; `Korchagin`; Thom (`Thom`); Shulman (`Shulman`) | Historical claim; nothing to formalize |
| 86 | 402–406 | Framework and permanence results. | `CDE`; `Korchagin`; `Shulman` | Attribution only |
| 87 | 406–408 | Non-approximability for finite Schatten norms. | `DGLT`; `LubotzkyOppenheim`; `Thom` | Not in repo; not used by any proof |
| 88 | 409–410 | Operator–Hilbert–Schmidt stability as a possible source of non-MF groups. | Bachner–Dogon–Lubotzky (`BDL`) | Not in repo; not used |
| 91 | 417–423 | One-sided compression makes a Kazhdan projection infinite in the full group `C*`-algebra; comparison with the present corona argument. | Tseng (`Tseng`) | **PARTIAL** — the present stable-finite corona route is formalized; Tseng's theorem is not |
| 92 / 227 | 425–428, 912 | Leavitt rank behavior and pure infinite simplicity / the operative sandwich form. | Leavitt (`Leavitt`); Abrams–Aranda Pino (`AbramsAranda`) | **PARTIAL** — positive-rank equivalences, `BinaryLeavitt.hasSingleSandwichDivision`, and `HasSingleSandwichDivision.isSimpleRing` are proved; the historical module-rank statement and a general `PurelyInfinite` predicate are not |
| 93 | 428 | "hence an exchange ring" | Ara (`AraExchange`) | **DISCHARGED IN-REPO** — `BinaryLeavitt.hasRightExchange` proves the standard one-element right-ideal exchange-ring property |
| 94 / 228 | 429, 913–915 | The center is the base field; over `F_2` the only central unit is `1`. | Aranda Pino–Crow (`ArandaCrow`) | **DISCHARGED IN-REPO** — `BinaryLeavitt.center_eq_bot`, `eq_smul_one_of_central`, and `central_units_trivial` |
| 95 | 429–432 | Preusser gives general normal-subgroup theorems over exchange rings; the present proof extracts a root directly. | Preusser (`Preusser`) | **PARTIAL** — the direct alternative is fully formalized; the general literature attribution is not |
| 96 / 218 / 262 | 433–435, 881–882, 1067–1069 | General property-(T) theorem for elementary groups over finitely generated rings. | Ershov–Jaikin-Zapirain (`EJZ`, Thm 1.1) | **PARTIAL** — the binary Leavitt cases used are proved in-repo; the general theorem is not |
| 97 | 436–437 | Related rigidity for metric approximations of Kazhdan groups. | `KT19`; Alekseev–Thom (`AlekseevThom`); Dadarlat (`Dadarlat`) | Not in repo; not used |
| 74 | 366–367 | "If `G` is amenable, its property-(T) subgroup `L` is finite." | Bekka–de la Harpe–Valette (`BHV`) | **DISCHARGED IN-REPO** — `Kazhdan.finite_of_isAmenable_of_kazhdan`, `finite_subgroup_of_isAmenable_of_kazhdan`; the citation is no longer load-bearing |
| 139 | 597–598 | "Let `P` be the image of the Kazhdan projection." | Akemann–Walter (`AkemannWalter`) | **PARTIAL** — the repo constructs `P` as a spectral projection of the orbit average (`KazhdanCompressionRep.proj`, `kt_08_kazhdan_projection`) rather than as the Akemann–Walter projection in `C*_max` |
| 274 | 1132–1134 | "The normal-form theorem for amalgamated free products shows that both vertex maps are injective." | folklore / Serre; used via mathlib | **DISCHARGED IN-REPO** — `Higman.Amalgam.of_injective_push` = `Monoid.PushoutI.of_injective` |

---

# Notes on the census method

* Rows are keyed to the current 1362-line `non_mf_groups_exist.tex`; the direct
  simplicity proof and every later row were re-keyed in this revision.
  `%`-comment lines (the `webmath` annotation blocks) are excluded: they are not
  printed, and their claims are restatements of the printed ones.
* Every declaration name in the "Lean declaration" column was grep-verified to
  exist.  Where a row cites a *clause* of a packaged `Prop` (e.g.
  `manuscriptOneSidedCompressionCriterion` cl. 2), the clause index refers to the
  conjunct order in the `def ... : Prop`.
* The single largest divergence between this census and
  `ONESIDED_TRANSPORT_LEDGER.md` is §4: the ledger marks `thm:normal-kazhdan`
  `closed`, which is correct, while this census marks five sentences of its
  *printed proof* `MISSING`, which is also correct.  Both facts matter: the
  theorem is unconditional, and the printed argument for it is not the
  formalized argument.
