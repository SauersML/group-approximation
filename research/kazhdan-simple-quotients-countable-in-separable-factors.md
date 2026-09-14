---
rg: 2
id: kazhdan-simple-quotients-countable-in-separable-factors
kind: claim
title: The unitary group of a separable II_1 factor contains only countably many of any family of pairwise distinct simple quotients of one Kazhdan group
artifacts:
  - research/artifacts/sk-strong-7-operator-algebras-2026-09-13.md
---

**ESTABLISHED (unreviewed).**
- **Setting.** Let `Λ` be a countable group with property (T) and let `{N_i}_{i∈I}` be pairwise distinct normal subgroups of `Λ` such that every quotient `Λ/N_i` is simple. Let `M` be a II_1 factor with separable predual.
- **Conclusion.** The set of `i ∈ I` such that the unitary group `U(M)` contains a subgroup isomorphic to `Λ/N_i` is at most countable.
- **Consequences.**
  - For each `i`, `L(Λ/N_i) ≅ L(Λ/N_j)` holds for only countably many `j`, since `L(Λ/N_j)` is separable and contains `Λ/N_j` in its unitary group.
  - If `I` is uncountable, the factors `L(Λ/N_i)` of the ICC quotients form uncountably many isomorphism classes, and no separable II_1 factor contains all of them.

**Credit.** This is the argument of N. Ozawa, *There is no separable universal II_1-factor*, Proc. Amer. Math. Soc. 132 (2004), no. 2, 487–490, doi:10.1090/S0002-9939-03-07127-2.
- Theorem 2 of the arXiv source (math/0210411v2) states the conclusion for Gromov–Olshanskii quotients of a torsion-free hyperbolic Kazhdan group.
- Its proof uses only property (T) of `Λ`, simplicity of the quotients, and distinctness of the kernels.
- The same paper, right after its Theorem 2, printed: "it would be interesting to know whether all (or at least one of) Γ_α's are embeddable into the unitary group U(R^ω)". Those groups are not known to be hyperlinear.
- Verbatim quotes are in the artifact, §2.

**Proof sketch** (full proof in `kazhdan-simple-quotients-countable-in-separable-factors-proof`):
1. Suppose uncountably many `i` qualify.
2. The resulting homomorphisms `u_i: Λ → U(M)` stay a uniform `δ` away from the trivial homomorphism on the trace vector.
3. Separability gives `i ≠ j` whose values on a Kazhdan set are `ε`-close.
4. Property (T), applied to `s ↦ u_i(s) J u_j(s) J` on `L²(M)`, gives an invariant vector `η` near `1̂`.
5. Its stabiliser under `u_i` contains `N_i N_j`, which is all of `Λ` because distinct maximal normal subgroups generate `Λ`.
6. That contradicts `δ`.

**Scope and model tests.**
- **SL_3(Z):** by Margulis's normal subgroup theorem it has only countably many normal subgroups, so no uncountable family exists. The lemma is vacuous there, not contradicted.
- **Simplicity:** it is used once, to get `N_i N_j = Λ`. For non-simple quotients the argument needs the image of `N_j` in `Λ/N_i` to be infinite.
- **Witness family:** the subshift groups `G_X` over a fixed alphabet (`separable-factors-hold-countably-many-subshift-groups`).
