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

1. **Kernel homology (part 1, Step A).** `H^*(Conf_n(C); Z)` is the
   Orlik–Solomon algebra, graded by partitions (Arnold 1969; Orlik–Solomon
   1980; Brieskorn 1973). Cabling kills `w_{i'i''}` and relabels the other
   generators. Its transpose sends a class of support size `m` to classes of
   support size `m` and `m + 1`. So the support filtration passes to the
   colimit. For `q ≥ 1` this gives a finite filtration of `H_q(K; Q)` by
   `V`-submodules, with graded pieces
   `C_c(Conf_m(C), Q) ⊗_{Q[Σ_m]} W_{m,q}` for `q + 1 ≤ m ≤ 2q`. An earlier
   direct-sum claim was false (part 1, A3).
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
   of `K → bV → V` has vanishing rows `q ≥ 1`: each graded piece in step 1 is
   V-acyclic by step 3, and V-acyclicity passes to extensions by the long exact
   sequence (part 1, A6). Row `q = 0` is `H_p(V; Q) = 0`
   for `p ≥ 1` (`thompson-v-is-integrally-acyclic`). So `H_n(bV; Q) = 0` for
   `n ≥ 1`.
