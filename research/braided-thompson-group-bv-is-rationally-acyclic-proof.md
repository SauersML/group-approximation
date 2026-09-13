---
rg: 2
id: braided-thompson-group-bv-is-rationally-acyclic-proof
kind: route
title: Configuration-module homology of the pure braided kernel plus labelled Thompson acyclicity give rational acyclicity of bV
target: braided-thompson-group-bv-is-rationally-acyclic
requires:
  - thompson-v-is-integrally-acyclic
  - labelled-thompson-groups-are-acyclic
artifacts:
  - research/artifacts/zp-braided-v-rational-acyclicity-2026-09-13-part1.md
  - research/artifacts/zp-braided-v-rational-acyclicity-2026-09-13-part2.md
  - research/artifacts/zp-braided-v-rational-acyclicity-2026-09-13-part3.md
---

Let `K = ker(bV → V)`, the colimit of pure braid groups under cabling.

1. **Kernel homology (part 1, Step A).** Cohen's computation of
   `H_*(Conf_n(R^2))` as the Gerstenhaber operad (Sinha, arXiv:math/0610236,
   Theorem 6.3) is used. Cabling is composition with the degree-0 product, and
   the bracket is a derivation. Grouping basis elements by support gives, for
   `q ≥ 1`, a `V`-isomorphism
   `H_q(K; Q) ≅ ⊕_{m=q+1}^{2q} C_c(Conf_m(C), Q) ⊗_{Q[Σ_m]} W_{m,q}`.
2. **Products of Cantor sets (part 2, Step B).** For `G = Q^j`, the labelled
   Thompson group `V(G) = C(C, Q^j) ⋊ V` is acyclic
   (`labelled-thompson-groups-are-acyclic`). The scaling automorphisms by
   `(Q^×)^j` force its Lyndon–Hochschild–Serre spectral sequence to degenerate.
   The multidegree-`(1, ..., 1)` summand shows that `C(C^j, Q)` is V-acyclic.
3. **Configuration modules (part 3, Step C).** Restriction to closed sets and
   Mayer–Vietoris over the diagonals of `C^m` show that `C_c(Conf_m(C), Q)` is
   V-acyclic. Averaging over `Σ_m` extends this to
   `C_c(Conf_m(C), Q) ⊗_{Q[Σ_m]} W`.
4. **Assembly (part 3, Step D).** The Lyndon–Hochschild–Serre spectral sequence
   of `K → bV → V` has vanishing rows `q ≥ 1`. Row `q = 0` is `H_p(V; Q) = 0`
   for `p ≥ 1` (`thompson-v-is-integrally-acyclic`). So `H_n(bV; Q) = 0` for
   `n ≥ 1`.
