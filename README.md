# Group Approximation

The remote `verified` branch is automatically fast-forwarded after every complete Lean Prover CI success on `main`. Use that for the most recent correct Lean code.

## A non-MF group

[`non_mf_groups_exist.tex`](non_mf_groups_exist.tex) proves that not every group is MF.

## A simple C*-algebra that is not K1-injective

Blackadar's *K-Theory for Operator Algebras* (1998, §8.1) records as open whether every unital simple C*-algebra is K1-injective, and Schafhauser, Tikuisis and White pose the question as Problem LIX of [Nuclear C*-algebras: 99 problems](https://arxiv.org/abs/2506.10902). The answer is no. [`k1_injectivity_counterexample.tex`](k1_injectivity_counterexample.tex) constructs a separable simple unital C*-algebra `A` with a unitary `u ∉ U₀(A)` such that `diag(u, 1) ∈ U₀(M₂(A))`. The Lean theorems are `NinetyNineProblems.not_problemLIX` and `exists_separable_simple_unital_not_k1Inj` in `GroupApproximation/Manuscript/NinetyNineProblems/ProblemLIX.lean`; the bundle obstruction they rest on is `CharClass.lemmaTwoHolds`. The Palomar registry surface is `Palomar/LIXChallenge.lean`, `Palomar/LIXSolution.lean` and `Palomar/comparator-lix.json`. The mod-2 singular cohomology under `GroupApproximation/CharClass/` is built on a port of [akopjan/HamSandwich](https://github.com/akopjan/HamSandwich); see `GroupApproximation/ThirdParty/HamSandwich/UPSTREAM.md`.

## Lean library

| Area | Directories | Contents |
| --- | --- | --- |
| Group theory | `Algebra/`, `GroupTheory/`, `Higman/`, `Covers/` | Presentations, normal forms, free products, HNN extensions, quotients, embeddings, and torsion |
| Finite approximation | `Sofic/`, `Criterion/`, `Stability/`, `Domination/`, `Matching/` | MF, sofic, and hyperlinear interfaces; finite models; residuals; matrix coronas; permanence and obstruction theorems |
| Rigidity | `PropertyT/`, `Kazhdan/`, `PropertyTT/` | Fixed-point methods, relative property (T), spectral and Hodge certificates, and property (TT)/T |
| Analysis | `Analysis/`, `KOne/`, `Leavitt/`, `Steinberg/` | Matrix estimates, projections, traces, C*-algebras, K-theory, and noncommutative rings |
| Other group constructions | `Kun/`, `KunThom/`, `Quantum/`, `Monsters/` | Graph, permutation, quantum, and embedding constructions |
| Public and checked interfaces | `Endpoint/`, `Meta/`, `Computability/`, `Manuscript/` | Stable exports, certificate replay, computability wrappers, statement matching, and axiom audits |
