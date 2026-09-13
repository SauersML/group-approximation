# Group Approximation

The remote `verified` branch is automatically fast-forwarded after every complete Lean Prover CI success on `main`. Use that for the most recent correct Lean code.

## A non-MF group

[`non_mf_groups_exist.tex`](non_mf_groups_exist.tex) proves that not every group is MF.

## A simple C*-algebra that is not K1-injective

Blackadar's *K-Theory for Operator Algebras* (1998, §8.1) records as open whether every unital simple C*-algebra is K1-injective, and Schafhauser, Tikuisis and White pose the question as Problem LIX of [Nuclear C*-algebras: 99 problems](https://arxiv.org/abs/2506.10902). The answer is no. [`k1_injectivity_counterexample.tex`](k1_injectivity_counterexample.tex) constructs a separable simple unital C*-algebra `A` with a unitary `u ∉ U₀(A)` such that `diag(u, 1) ∈ U₀(M₂(A))`. The Lean theorems are `NinetyNineProblems.not_problemLIX` and `exists_separable_simple_unital_not_k1Inj` in `GroupApproximation/Manuscript/NinetyNineProblems/ProblemLIX.lean`; the bundle obstruction they rest on is `CharClass.lemmaTwoHolds`. The Palomar registry surface is `Palomar/LIXChallenge.lean`, `Palomar/LIXSolution.lean` and `Palomar/comparator-lix.json`. The mod-2 singular cohomology under `GroupApproximation/CharClass/` is built on a port of [akopjan/HamSandwich](https://github.com/akopjan/HamSandwich); see `GroupApproximation/ThirdParty/HamSandwich/UPSTREAM.md`.

## A surjunctive group that is not sofic

Gromov and Weiss proved that every sofic group is surjunctive. The converse is recorded as open by Arzhantseva and Gal in 2013, on page 127 of [On approximation properties of semidirect products of groups](https://arxiv.org/abs/1312.7682): "It is still unknown whether every group is surjunctive and whether there exists a non-sofic surjunctive group." Bowen and Chapman print it as Problem 1.1 of [Surjunctivity does not characterize cosoficity of invariant random subgroups](https://arxiv.org/abs/2511.06586), with the references [Gro99, Wei00] to Gromov and Weiss, verbatim:

> Are all surjunctive groups sofic? Namely, does surjunctivity characterize soficity?

The answer is no. The witness is the symmetric double `G *_Γ G` of the pair

```text
Γ = EL₃(𝔽₂[x₁, x₂, x₃])  ≤  G = EL₃(𝔽₂[x₁^±¹, x₂^±¹, x₃^±¹]) ⋊ EL₃(ℤ),
```

with `EL₃(ℤ)` acting on the Laurent exponents by monomial substitution. Reducing exponents modulo `n` gives a separating family of finite quotients, so `G` is residually finite (`ambient_residuallyFinite` in `GroupApproximation/BowenChapman/LaurentPairResiduallyFinite.lean`); a residually finite group is surjunctive and the symmetric double of a surjunctive group is surjunctive over every subgroup (`GroupApproximation/Dynamics/SurjunctivityTransfer.lean`, `GroupApproximation/Dynamics/DoubleFinitarySite.lean`). Both `G` and `Γ` have property (T) (`GroupApproximation/BowenChapman/LaurentPairKazhdan.lean`), and `Γ` is infranormal in `G` without being normal (`GroupApproximation/BowenChapman/LaurentPairInfranormal.lean`). For such a pair Kun and Thom, [arXiv:2608.06222](https://arxiv.org/abs/2608.06222), Theorem A, show that the double is not sofic. That rests on the permutation centralizer normalization theorem of their Theorem 4.1, which is proved here in a general sequential form, in `GroupApproximation/KunThom/CompressorNormalizationCore.lean`, and the nonsoficity of the double is derived from it here; the pair itself is the q = 2, r = d = 3 member of the family in their Theorem E, with `EL₃(ℤ)` in place of `SL₃(ℤ)`. The endpoint is `exists_fg_surjunctive_not_isSofic` in `GroupApproximation/BowenChapman/Endpoint.lean`.

Kun and Thom mention surjunctivity only in their introduction's history of Gromov's theorem, and their doubles were not known to be surjunctive: as late as 6 August 2026, OpenAI's *Ten Advances in Mathematics and Theoretical Computer Science* records the question as open (Chapter 3, page 79: "We do not know whether R× is surjunctive. A positive answer would produce a surjunctive nonsofic group"). The new ingredient here is the surjunctivity half, `isSurjunctive_symmetricDouble`, that the symmetric double of a surjunctive group is surjunctive over every subgroup. With `Γ` trivial this is the free product `G * G`, a case of the product question that Arzhantseva and Gal record as open, citing Weiss (2000); Doucha and Gismatullin still state the free-product case `ℤ * G` as a conjecture ([On dual surjunctivity and applications](https://doi.org/10.4171/GGD/681), Groups Geom. Dyn. 16 (2022), Conjecture 3.12), and we have found no later resolution.

The problem was solved by Astra, using a custom proof tool. All prose for this result, this section included, and the Lean formalisation were produced by Claude (Anthropic) under the author's direction. The argument was committed here on 2026-09-12 (commit 05a8aff7a) and the Lean endpoint landed the same day (commit 92ad0059d).

The Palomar registry surface is `Palomar/BowenChapmanChallenge.lean`, `Palomar/BowenChapmanSolution.lean` and `Palomar/comparator-bowen-chapman.json`, with the theorems `BowenChapman.exists_finitelyGenerated_surjunctive_not_sofic` and `BowenChapman.not_all_surjunctive_groups_sofic`. Both use `propext`, `Classical.choice` and `Quot.sound` and nothing else. The source-level checks need no Lean:

```sh
python3 scripts/check_palomar_submission.py --self-test
python3 scripts/check_palomar_submission.py
```

The kernel replay is Comparator on that configuration, which the `Palomar comparator` workflow runs with `config=Palomar/comparator-bowen-chapman.json`:

```sh
lake exe cache get
lake build PalomarBowenChapmanChallenge PalomarBowenChapmanSolution
lake env comparator Palomar/comparator-bowen-chapman.json
```

The repository holds one `formalization.yaml` and one Comparator configuration per submission: `Palomar/comparator-lix.json` for the K1-injectivity result above, `Palomar/comparator-bowen-chapman.json` for this one. They share the Lean development and no mathematics. Everything here is released under Apache-2.0, in `LICENSE`.

## Lean library

| Area | Directories | Contents |
| --- | --- | --- |
| Group theory | `Algebra/`, `GroupTheory/`, `Higman/`, `Covers/` | Presentations, normal forms, free products, HNN extensions, quotients, embeddings, and torsion |
| Finite approximation | `Sofic/`, `Criterion/`, `Stability/`, `Domination/`, `Matching/` | MF, sofic, and hyperlinear interfaces; finite models; residuals; matrix coronas; permanence and obstruction theorems |
| Rigidity | `PropertyT/`, `Kazhdan/`, `PropertyTT/` | Fixed-point methods, relative property (T), spectral and Hodge certificates, and property (TT)/T |
| Analysis | `Analysis/`, `KOne/`, `Leavitt/`, `Steinberg/` | Matrix estimates, projections, traces, C*-algebras, K-theory, and noncommutative rings |
| Other group constructions | `Kun/`, `KunThom/`, `Quantum/`, `Monsters/` | Graph, permutation, quantum, and embedding constructions |
| Public and checked interfaces | `Endpoint/`, `Meta/`, `Computability/`, `Manuscript/` | Stable exports, certificate replay, computability wrappers, statement matching, and axiom audits |
