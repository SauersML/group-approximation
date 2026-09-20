# Group Approximation

The remote `verified` branch is automatically fast-forwarded after every complete Lean Prover CI success on `main`. Use that for the most recent correct Lean code.

## A non-MF group

[`non_mf_groups_exist.tex`](non_mf_groups_exist.tex) answers the
[MF-group problem](https://arxiv.org/html/2508.17392v1#S1) negatively:
not every group admits faithful asymptotic matrix representations in operator
norm. The proof uses one-sided compression of Kazhdan subgroups and a
projection-corner argument to force nontrivial elements to vanish in every
norm matrix corona. It also constructs sofic groups that are not MF.

## Named problems solved here

The following are original written solutions to named questions, selected
using the dated proofs and literature checks in [Cairn](research/).
Each entry identifies the question, the new argument, and its precise scope.

| Problem | Result and argument | Our proof |
| --- | --- | --- |
| **The trace problem — STW XXII.** [Schafhauser–Tikuisis–White, §7](https://arxiv.org/html/2506.10902v2#S7). | **Negative.** A separable unital nuclear type I algebra has a uniform tracial completion with an additional trace that is not continuous in the uniform 2-norm. A growing projective-bundle construction produces a character detecting elements whose uniform 2-norm tends to zero. | [Counterexample and proof](research/artifacts/stw22-trace-problem-counterexample-audit-2026-08-31.md). |
| **Explicit automorphism loops — STW L, Kirchberg alternative.** [Schafhauser–Tikuisis–White, §14](https://arxiv.org/html/2506.10902v2#S14). | **Six generators constructed.** Circle actions on two finite graph models give an integral basis of the automorphism fundamental group of the Kirchberg counterpart of the irrational rotation algebra. The construction uses fixed classification isomorphisms; explicit generators in the stably finite rotation algebra remain open. | [Six-loop construction](research/artifacts/stw50-six-kirchberg-loops-2026-09-05.md). |
| **K₁-injectivity of simple C*-algebras — STW LIX.** [Schafhauser–Tikuisis–White, §17](https://arxiv.org/html/2506.10902v2#S17). | **Negative.** A separable simple unital algebra has a unitary outside its identity component whose first matrix stabilization is null-homotopic. A twisted bundle obstruction survives the connecting maps that make the inductive limit simple. | [Manuscript](k1_injectivity_counterexample.tex); [AH construction](research/artifacts/stw59-simple-ah-k1-counterexample-manuscript-2026-09-05.md). |
| **Vaidyanathan's rational K-stability question for AH algebras.** Informal question in [Sarkar's compendium, §20, p. 48](https://www.isibang.ac.in/~jay/papers/oaotINSA.pdf). | **Negative for AH algebras built from compact homogeneous blocks.** A simple unital monotracial AH algebra is rationally K-stable but not integrally K-stable. A real-projective Euler tower preserves an integral torsion obstruction while establishing rational stability in every positive homotopy degree. | [Torsion Euler tower](research/artifacts/stw59-rational-k-stability-torsion-euler-tower-2026-09-05.md); [exact scope](research/artifacts/rational-k-stability-ah-literature-boundary-2026-09-05.md). |
| **Berlai's mixed-conjugator one-relator question.** [Berlai, introduction](https://arxiv.org/html/2502.05064v1). | **Positive.** With `x^y = y⁻¹xy`, the group `⟨a,b ∣ a^(a^(b⁻¹ab²)) = a²⟩` is sofic. A triangular cyclic-amalgam construction proves this and the broader family with conjugator `b^p a^s b^q`. | [One-sided and single-block conjugator proof](research/artifacts/mixed-conjugator-one-relator-proof-2026-09-07.md). |
| **Does surjunctivity characterize soficity?** [2010 book](https://doi.org/10.1007/978-3-642-14034-1); [2025 formulation](https://arxiv.org/html/2511.06586v1). | **Negative, even for finitely presented groups.** A new surjunctivity permanence argument for group doubles, using finite-support quotients and stabilizer intersections, applies to a Kun–Thom nonsofic double. | [Finitely presented witness](research/artifacts/fp-surjunctive-nonsofic-double-2026-09-11.md); [surjunctivity theorem](research/artifacts/finitary-split-extension-surjunctivity-2026-09-11.md). |
| **Guba's Ore equation — Question 1 / survey Question 3.20.** [Original question](https://arxiv.org/abs/2201.02308); [survey](https://gcc.episciences.org/11315/pdf). | **Positive.** For every field `K` and nonzero `b ∈ K[F]`, `(1 − x₁)u = bv` has a nonzero solution. An induction through the nested supports of conjugates of `x₁` extends Guba's `x₀` theorem. This settles the specified equation, not amenability of Thompson's group `F`. | [Complete proof](research/thompson-f-one-minus-x1-is-ore-with-every-element-proof.md); [source and priority check](research/artifacts/guba-q1-novelty-2026-09-12.md). |
| **A type [A₂] action with non-finitely-presented image — Fournier-Facio–Wu–Zaremsky Question 5.8.** [Problem statement](https://arxiv.org/html/2603.24687v2#S5). | **Positive.** A diagonal Thompson-group normalizer produces a type `[A₂]` action of a finitely presented group whose faithful image is not finitely presented. The construction verifies the stabilizer conditions and computes the action kernel; it answers this question without resolving Boone–Higman. | [Construction and proof](research/a2-non-fp-image-via-diagonal-normalizer-proof.md); [question and scope](research/a2-action-with-non-finitely-presented-image.md). |

## Baum–Connes: integrated further attempt

The [further attempt and proofs](research/artifacts/Cairn_Baum_Connes_General_Attempt.md)
are integrated into Cairn with dependency routes. They prove trace
factorization for amenable-kernel relation quotients and locate the
missing module obstruction as a nonzero liftable quotient K-class.
All bounded positive traces miss its degree-zero candidates; the torus
example explains why that does not prove vanishing. **General reduced
Baum–Connes with trivial coefficients remains unresolved in this
development.** This integration supplies no counterexample or general
assembly inverse.

## A simple C*-algebra that is not K1-injective

Blackadar's *K-Theory for Operator Algebras* (1998, §8.1) records as open whether every unital simple C*-algebra is K1-injective, and Schafhauser, Tikuisis and White pose the question as Problem LIX of [Nuclear C*-algebras: 99 problems](https://arxiv.org/abs/2506.10902). The answer is no. [`k1_injectivity_counterexample.tex`](k1_injectivity_counterexample.tex) constructs a separable simple unital C*-algebra `A` with a unitary `u ∉ U₀(A)` such that `diag(u, 1) ∈ U₀(M₂(A))`. The Lean theorems are `NinetyNineProblems.not_problemLIX` and `exists_separable_simple_unital_not_k1Inj` in `GroupApproximation/Manuscript/NinetyNineProblems/ProblemLIX.lean`; the bundle obstruction they rest on is `CharClass.lemmaTwoHolds`. The Palomar registry surface is `Palomar/LIXChallenge.lean`, `Palomar/LIXSolution.lean` and `Palomar/comparator-lix.json`. The mod-2 singular cohomology under `GroupApproximation/CharClass/` is built on a port of [akopjan/HamSandwich](https://github.com/akopjan/HamSandwich); see `GroupApproximation/ThirdParty/HamSandwich/UPSTREAM.md`.

## A surjunctive group that is not sofic

Gromov and Weiss proved that every sofic group is surjunctive. Ceccherini-Silberstein and Coornaert ask for the converse in 2010, as open problem (OP-11) of [Cellular Automata and Groups](https://doi.org/10.1007/978-3-642-14034-1): "Does there exist a surjunctive group which is non-sofic?" The [second edition](https://doi.org/10.1007/978-3-031-43328-3), published in January 2024 with copyright year 2023, retains OP-11 on page 527 and explicitly confirms that its problem list appeared in the first edition. This substantiates the 2010 formulation; the first proposer has not been established. Arzhantseva and Gal record it as open in their [2013 preprint](https://arxiv.org/abs/1312.7682), page 3, subsequently published in 2020 in *Annales Mathématiques Blaise Pascal* 27(1), page 127, and Bowen and Chapman print it as Problem 1.1 of [Surjunctivity does not characterize cosoficity of invariant random subgroups](https://arxiv.org/abs/2511.06586):

> Are all surjunctive groups sofic? Namely, does surjunctivity characterize soficity?

The answer is no. The witness is the symmetric double `G *_Γ G` of the pair

```text
Γ = EL₃(𝔽₂[x₁, x₂, x₃])  ≤  G = EL₃(𝔽₂[x₁^±¹, x₂^±¹, x₃^±¹]) ⋊ EL₃(ℤ),
```

with `EL₃(ℤ)` acting on the Laurent exponents by monomial substitution. Reducing exponents modulo `n` gives a separating family of finite quotients, so `G` is residually finite (`ambient_residuallyFinite` in `GroupApproximation/SurjunctiveNonsofic/LaurentPairResiduallyFinite.lean`); a residually finite group is surjunctive and the symmetric double of a surjunctive group is surjunctive over every subgroup (`GroupApproximation/Dynamics/SurjunctivityTransfer.lean`, `GroupApproximation/Dynamics/DoubleFinitarySite.lean`). Both `G` and `Γ` have property (T) (`GroupApproximation/SurjunctiveNonsofic/LaurentPairKazhdan.lean`), and `Γ` is infranormal in `G` without being normal (`GroupApproximation/SurjunctiveNonsofic/LaurentPairInfranormal.lean`). For such a pair Kun and Thom, [arXiv:2608.06222](https://arxiv.org/abs/2608.06222), Theorem A, show that the double is not sofic. That rests on the permutation centralizer normalization theorem of their Theorem 4.1, which is proved here in a general sequential form, in `GroupApproximation/KunThom/CompressorNormalizationCore.lean`, and the nonsoficity of the double is derived from it here; the pair itself is the q = 2, r = d = 3 member of the family in their Theorem E, with the acting group `SL₃(ℤ)` written as `EL₃(ℤ)`, which is the same group. The endpoint is `exists_fg_surjunctive_not_isSofic` in `GroupApproximation/SurjunctiveNonsofic/Endpoint.lean`.

Kun and Thom supply the construction and its nonsoficity; their cited paper does not prove surjunctivity. The new ingredient here is the surjunctivity half, `isSurjunctive_symmetricDouble`, that the symmetric double of a surjunctive group is surjunctive over every subgroup. With `Γ` trivial this is the free product `G * G` (`isSurjunctive_coprodI_double` in `GroupApproximation/Dynamics/FreeProductSurjunctivity.lean`), a case of the product question that Arzhantseva and Gal record as open, citing Weiss (2000); Doucha and Gismatullin still state the free-product case `ℤ * G` as a conjecture ([On dual surjunctivity and applications](https://doi.org/10.4171/GGD/681), Groups Geom. Dyn. 16 (2022), Conjecture 3.12).

The surjunctivity argument was developed by Astra using a custom proof tool. Claude (Anthropic) produced the original exposition and Lean formalization under the user's direction; Codex (OpenAI) reviewed the proof, literature, and credits and revised this account. The argument was committed here on 2026-09-12 UTC (commit 05a8aff7a; September 11 in Chicago), and the Lean endpoint landed the same UTC day (commit 92ad0059d). Classical inputs include Lawton's residual-finiteness and subgroup results and the Curtis–Hedlund–Lyndon theorem. [Arzhantseva–Gal's extension theorem](https://doi.org/10.5802/ambp.386) requires a finitely generated residually finite kernel, so it does not directly cover this double's infinite-rank free fold kernel.

The preparation materials are [the overview](Palomar/SurjunctiveNonsoficOverview.txt), [the source metadata](metadata/palomar-surjunctive-nonsofic.yaml), and [the exact submission details and verification runs](Palomar/SurjunctiveNonsoficSubmission.txt). Revision `232c77f169ec66b27fd480d5c19474f519d359b7` was submitted to Palomar as `e8sd7sbrpcxh` on September 14, 2026 UTC; [Palomar's automated verification](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/34794577299) is separate from the repository checks. The earlier submission remains withdrawn.

The Palomar registry surface is `Palomar/SurjunctiveNonsoficChallenge.lean`, `Palomar/SurjunctiveNonsoficSolution.lean` and `Palomar/comparator-surjunctive-nonsofic.json`, with the theorems `SurjunctiveNonsofic.exists_finitelyGenerated_surjunctive_not_sofic` and `SurjunctiveNonsofic.not_all_surjunctive_groups_sofic`. Both use `propext`, `Classical.choice` and `Quot.sound` and nothing else. The source-level checks need no Lean:

```sh
python3 scripts/check_palomar_submission.py --self-test
python3 scripts/check_palomar_submission.py
```

The kernel replay is Comparator on that configuration, which the `Palomar comparator` workflow runs with `config=Palomar/comparator-surjunctive-nonsofic.json`:

```sh
lake exe cache get
lake build PalomarSurjunctiveNonsoficChallenge PalomarSurjunctiveNonsoficSolution
lake env comparator Palomar/comparator-surjunctive-nonsofic.json
```

## An infinite simple group with property (T) that is sofic

Brown asks in 2001, as Question 11.7 of [Tracial invariants, classification and II₁ factor representations of Popa algebras](https://arxiv.org/abs/math/0111286), whether an infinite simple discrete group with Kazhdan's property (T) can embed in the unitary group of an R^ω-embeddable McDuff factor, which for such a group is the same as being hyperlinear. Ozawa asks it in that language in 2003, in [About the QWEP conjecture](https://arxiv.org/abs/math/0306067) (Internat. J. Math. 15 (2004)). Pestov prints the question, citing Ozawa and adding the sofic form, as Open question 9.1 of [Hyperlinear and sofic groups: a brief guide](https://arxiv.org/abs/0804.3968) (Bull. Symbolic Logic 14 (2008)): can an infinite simple group with Kazhdan's property (T) be hyperlinear, or sofic? The answer is yes, in both forms. The witness is `EL₃(A)` for the finitely generated ring `A = LC(X, 𝔽₂) ⋊ ℤ` over the Toeplitz subshift `X`: it is infinite, simple, has property (T) and is LEF, so it is sofic and hyperlinear. The endpoint is `exists_infinite_simple_kazhdan_lef` in `GroupApproximation/Pestov91/WitnessAssembly.lean`. The argument was committed here on 2026-09-13 (commit f375478c7) and the Palomar theorems were proved the same day (commit 5f9c16b7b).

The compared theorems are existence statements through this one witness: the binary Toeplitz subshift, the field `𝔽₂`, and no quotient by the center, which is trivial. They do not register the more general statement, over every finite field and every infinite minimal subshift, that the informal argument treats. The formal proof, in `GroupApproximation/Pestov91/`, establishes finite generation of `A` (`WitnessRing.lean`), simplicity of `A` and triviality of its center for a free minimal action (`RingSimple.lean`, `WitnessCentre.lean`), simplicity of `EL₃(A)` from those by split annihilators and root extraction (`SplitSimplicity.lean`, `WitnessSimple.lean`), infiniteness of `EL₃(A)` from the infinite ring (`Centre.lean`, `CentreSkew.lean`), property (T) by the Ershov–Jaikin-Zapirain theorem proved in this repository (`Kazhdan.lean`), and the LEF property of `A` from periodic models of the Toeplitz sequence (`ToeplitzModel.lean`, `LEFCrossedProduct.lean`, `LEFWitness.lean`); LEF groups are sofic and sofic groups are hyperlinear (`GroupApproximation/Sofic/LEFSofic.lean`, `GroupApproximation/Sofic/Hyperlinear.lean`).

The Palomar registry surface is `Palomar/Pestov91Challenge.lean`, `Palomar/Pestov91Solution.lean` and `Palomar/comparator-pestov91.json`, with the theorems `Pestov91.exists_infinite_simple_propertyT_hyperlinear` and `Pestov91.exists_infinite_simple_propertyT_sofic`. Both use `propext`, `Classical.choice` and `Quot.sound` and nothing else. The problem was solved by Claude (Anthropic) under the user's direction, using the custom proof tool [Cairn](https://github.com/SauersML/Cairn), and the argument was reviewed in two separate Claude Code agent sessions. Claude (Anthropic) wrote the prose of the submission itself: this section, the registry abstract and narrative fields preserved in `metadata/palomar-pestov91.yaml`, and the docstrings of the Palomar Pestov91 modules. It also produced the Lean formalization, under the user's direction. The source-level checks need no Lean:

```sh
python3 scripts/check_palomar_submission.py --self-test
python3 scripts/check_palomar_submission.py
```

The kernel replay is Comparator on that configuration, which the `Palomar comparator` workflow runs with `config=Palomar/comparator-pestov91.json`, with NanoDa as a second kernel:

```sh
lake exe cache get
lake build PalomarPestov91Challenge PalomarPestov91Solution
lake env lean scripts/PalomarPestov91Axioms.lean
lake env comparator Palomar/comparator-pestov91.json
```

## A type [A₂] action with a non-finitely-presented image

Fournier-Facio, Wu and Zaremsky ask, as Question 5.8 of [Abstract twisted Brin–Thompson groups](https://arxiv.org/abs/2603.24687) (p. 27), whether some group action `G ↷ S` of type [A₂] has a quotient `G/ker(G ↷ S)` that is not finitely presented. The answer is yes. The witness is built from Thompson's group `F` acting on the positive dyadic rationals, and the endpoint is `question58` in `GroupApproximation/TypeA2/Answer.lean`. The answer and its Palomar pair landed on 2026-09-13 (commit e8abf9a00).

The Palomar registry surface is `Palomar/TypeA2Challenge.lean`, `Palomar/TypeA2Solution.lean` and `Palomar/comparator-type-a2.json`, with the theorem `FFWZ.exists_isTypeA2_quotient_not_isFinitelyPresented`. It uses `propext`, `Classical.choice` and `Quot.sound` and nothing else. The problem was solved by Astra, using a custom proof tool. All prose for this result, this section included, and the Lean formalization were produced by Claude (Anthropic) under the user's direction.

## The equation (1 − x₁) u = b v in the group ring of Thompson's group F

Guba asks, as Question 3.20 of [Amenability problem for Thompson's group F: state of the art](https://arxiv.org/abs/2305.07113) (Groups Complexity Cryptology 15 (2023), p. 3:18), and as Question 1 of [arXiv:2201.02308](https://arxiv.org/abs/2201.02308), whether for a field `K` and every `b ∈ K[F]` the equation `(1 − x₁) u = b v` has a non-zero solution in `K[F]`. Guba's Theorem 3.18 gives one with `x₀` in place of `x₁`. The answer is yes, and for `b ≠ 0` the common multiple `b v` can be taken non-zero. The development proves that `K[F]` has no zero divisors, Theorem 3.18, and that `x₁` lies in a subgroup `H`, with an isomorphism `H → F` sending `x₁` to `x₀`, which contains or is contained in each of its conjugates. The endpoint is `one_sub_x1_solution` in `GroupApproximation/ThompsonOre/X1AnswerThompson.lean`, and the Palomar theorems were proved on 2026-09-13 (commit 6b308147b).

The Palomar registry surface is `Palomar/GubaThompsonChallenge.lean`, `Palomar/GubaThompsonSolution.lean` and `Palomar/comparator-guba-thompson.json`, with the theorems `GubaThompson.question_3_20` and `GubaThompson.question_3_20_common_multiple`. Both use `propext`, `Classical.choice` and `Quot.sound` and nothing else. The problem was solved by Astra, using a custom proof tool. All prose for this result, this section included, and the Lean formalization were produced by Claude (Anthropic) under the user's direction.

## Commuting sofic actions that do not combine to a sofic action

Gao, Kunnawalkam Elayavalli and Patchell ask, as Question 4.2 of [Soficity for group actions on sets and applications](https://arxiv.org/abs/2401.04945) (Res. Math. Sci. 12 (2025), article 48, p. 14), whether commuting actions `α_i : G_i ↷ X` of countable groups on a countable set combine to a sofic action of `⊕_i G_i` exactly when every `α_i` is sofic. The forward direction is their Proposition 2.15(3); the converse fails. The witness is `X = (G × G)/ΔΓ` for an explicit Kun–Thom pair `Γ ≤ G` ([arXiv:2608.06222](https://arxiv.org/abs/2608.06222)), with `G × G` acting by left multiplication. Both coordinate actions of `G` are free and `G` is residually finite, so both are sofic, while the diagonal orbit of the base coset is the coset `G`-set `G/Γ`, which is not sofic. The endpoint is `exists_commuting_sofic_actions_not_sofic` in `GroupApproximation/CommutingSoficActions/Endpoint.lean`. The argument was committed here on 2026-08-18 (commit 393a096b6), the Lean endpoint landed on 2026-09-13 (commit 29e593abf) and the Palomar pair the same day (commit 3f1af7161).

The Palomar registry surface is `Palomar/GKPCommutingActionsChallenge.lean`, `Palomar/GKPCommutingActionsSolution.lean` and `Palomar/comparator-gkp-commuting-actions.json`, with the theorems `GKPCommutingActions.commuting_sofic_actions_need_not_combine` and `GKPCommutingActions.exists_commuting_sofic_actions_not_sofic`. Both use `propext`, `Classical.choice` and `Quot.sound` and nothing else. The problem was solved by Astra, using a custom proof tool. All prose for this result, this section included, and the Lean formalization were produced by Claude (Anthropic) under the user's direction.

## An amenable trace that is not quasidiagonal

Schafhauser, Tikuisis and White ask, as Problem X(1) of [Nuclear C*-algebras: 99 problems](https://arxiv.org/abs/2506.10902) (v2, p. 15), whether amenable traces on C*-algebras are necessarily quasidiagonal. The question is N. P. Brown's, from *Invariant means and finite representation theory of C*-algebras* (Mem. Amer. Math. Soc. 184 (2006), no. 865). The answer is no. The witness is the maximal group C*-algebra of the development's group `MarkedGroup` with its canonical tracial state, which is amenable and not quasidiagonal. The endpoint is `amenableNonQuasidiagonalTrace` in `GroupApproximation/Manuscript/NinetyNineProblems/ProblemXWitness.lean`, and `GroupApproximation/PalomarBridges/X1.lean` moves the witness to `Type` through `Shrink`. The counterexample was proved here on 2026-08-31 (commit 4830b808c) and the Palomar pair landed on 2026-09-13 (commit 0badf535c).

The Palomar registry surface is `Palomar/STWProblemX1Challenge.lean`, `Palomar/STWProblemX1Solution.lean` and `Palomar/comparator-stw-x1.json`, with the theorems `STWProblemX1.exists_separable_amenable_not_quasidiagonal` and `STWProblemX1.not_every_amenable_trace_quasidiagonal`. Both use `propext`, `Classical.choice` and `Quot.sound` and nothing else. The problem was solved by Astra, using a custom proof tool. All prose for this result, this section included, was written by Claude (Anthropic). Its Lean formalization was produced by AI coding agents, Codex (OpenAI) and Claude (Anthropic), under the user's direction.

## A tracial completion with a discontinuous trace

Schafhauser, Tikuisis and White ask, as Problem XXII of [Nuclear C*-algebras: 99 problems](https://arxiv.org/abs/2506.10902) (v2, p. 24), whether for a C*-algebra `A` with non-empty compact trace space all traces on the uniform tracial completion `Ā^{T(A)}` are automatically `‖·‖_{2,T(A)}`-continuous, that is, whether the canonical embedding `T(A) ⊆ T(Ā^{T(A)})` is an equality. The problem is the instance `M = Ā^{T(A)}` of Question 1.1 of [Tracially complete C*-algebras](https://arxiv.org/abs/2310.20594), which asks the same of every factorial tracially complete C*-algebra `(M, X)`. The answer is no. The witness is the development's C*-algebra `AntipodalCounterexampleAlgebra`, its uniform tracial completion `AntipodalCompletionAlgebra` and the set `antipodalDesignatedTraces` of canonical extensions of its traces. The development proves that this pair is factorial tracially complete, that its `‖·‖_{2,X}`-continuous traces are exactly the designated ones, and that some trace on the completion is not one of them. The endpoint is `antipodalFactorialNegativeSolutionToProblemXXII` in `GroupApproximation/Analysis/STW22AntipodalFactorialPair.lean`, and `GroupApproximation/PalomarBridges/XXII.lean` proves that restriction is a bijection from the designated traces onto `T(A)`, that the image of `A` is `‖·‖_{2,X}`-dense in the completion, and that `A` is separable. The Palomar pair landed on 2026-09-13 (commit 8444aeb6c).

The Palomar registry surface is `Palomar/STWProblemXXIIChallenge.lean`, `Palomar/STWProblemXXIISolution.lean` and `Palomar/comparator-stw-xxii.json`, with the theorems `STWProblemXXII.exists_uniformTracialCompletion_with_discontinuous_trace` and `STWProblemXXII.exists_factorial_traciallyComplete_with_discontinuous_trace`. Both use `propext`, `Classical.choice` and `Quot.sound` and nothing else. The problem was solved by Astra, using a custom proof tool. All prose for this result, this section included, was written by Claude (Anthropic). Its Lean formalization was produced by AI coding agents, Codex (OpenAI) and Claude (Anthropic), under the user's direction.

## A properly infinite Toeplitz algebra

Blanchard asks, as Question 5.4 of [arXiv:1507.02535](https://arxiv.org/abs/1507.02535) (v1, p. 9, also in [arXiv:1312.7722](https://arxiv.org/abs/1312.7722)), "But is 𝒯(E_DD) properly infinite?" Here `E_DD` is the Hilbert `C(B_∞)`-module over the complex Hilbert cube `B_∞` built in the proof of Proposition 4.3 of that preprint, and `𝒯(E_DD)` is the unital C*-algebra of operators on the Fock module of `E_DD` generated by the creation operators (Definition 5.1 there). The answer is yes: `𝒯(E_DD)` contains two isometries with mutually orthogonal range projections. The Dixmier–Douady obstruction has codimension one in `E_DD` and disappears in `E_DD ⊗ E_DD`, which has two orthonormal sections, and the isometries are creation operators of such sections. The endpoint is `exists_properlyInfinite_of_coeff` in `GroupApproximation/Toeplitz/Wick.lean`. The answer was committed here on 2026-09-13 (commit 412dd7632), and the Lean development and the Palomar pair landed the same day (commit 4caf6aea2).

The Palomar registry surface is `Palomar/BlanchardToeplitzChallenge.lean`, `Palomar/BlanchardToeplitzSolution.lean` and `Palomar/comparator-blanchard-toeplitz.json`, with the theorem `BlanchardToeplitz.blanchard_question_5_4`. It uses `propext`, `Classical.choice` and `Quot.sound` and nothing else. The problem was solved by Astra, using a custom proof tool. All prose for this result, this section included, and the Lean formalization were produced by Claude (Anthropic) under the user's direction.

The repository holds one Comparator configuration per submission, and `formalization.yaml` describes one submission at a time, currently `Palomar/comparator-surjunctive-nonsofic.json`; the other configurations receive their metadata when they are submitted. The configurations are `Palomar/comparator-lix.json` for the K1-injectivity result, `Palomar/comparator-surjunctive-nonsofic.json` for the surjunctive non-sofic group, and `Palomar/comparator-pestov91.json`, `Palomar/comparator-type-a2.json`, `Palomar/comparator-guba-thompson.json`, `Palomar/comparator-gkp-commuting-actions.json`, `Palomar/comparator-stw-x1.json`, `Palomar/comparator-stw-xxii.json` and `Palomar/comparator-blanchard-toeplitz.json` for the seven results after it. Each is its own `config` for the `Palomar comparator` workflow. They share the Lean development and no mathematics. Everything here is released under Apache-2.0, in `LICENSE`.

## Lean library

| Area | Directories | Contents |
| --- | --- | --- |
| Group theory | `Algebra/`, `GroupTheory/`, `Higman/`, `Covers/` | Presentations, normal forms, free products, HNN extensions, quotients, embeddings, and torsion |
| Finite approximation | `Sofic/`, `Criterion/`, `Stability/`, `Domination/`, `Matching/` | MF, sofic, and hyperlinear interfaces; finite models; residuals; matrix coronas; permanence and obstruction theorems |
| Rigidity | `PropertyT/`, `Kazhdan/`, `PropertyTT/` | Fixed-point methods, relative property (T), spectral and Hodge certificates, and property (TT)/T |
| Analysis | `Analysis/`, `KOne/`, `Leavitt/`, `Steinberg/` | Matrix estimates, projections, traces, C*-algebras, K-theory, and noncommutative rings |
| Other group constructions | `Kun/`, `KunThom/`, `Quantum/`, `Monsters/` | Graph, permutation, quantum, and embedding constructions |
| Public and checked interfaces | `Endpoint/`, `Meta/`, `Computability/`, `Manuscript/` | Stable exports, certificate replay, computability wrappers, statement matching, and axiom audits |


## Group property atlas

[Group Atlas](https://sauersml.github.io/group-atlas/) explores intersections
of group properties with sourced witnesses and impossibility proofs.
Its source lives in [SauersML/group-atlas](https://github.com/SauersML/group-atlas).
