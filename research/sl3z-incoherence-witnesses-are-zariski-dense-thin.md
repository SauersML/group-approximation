---
rg: 2
id: sl3z-incoherence-witnesses-are-zariski-dense-thin
kind: claim
title: A finitely generated non-finitely-presented subgroup of SL_3(Z) is a Zariski-dense thin group outside the tree hierarchy
artifacts:
  - research/artifacts/zp-sl3z-coherence-non-dense-2026-09-13-part1.md
---

Let `H_0` be the set of subgroups of `SL_3(Z)` that are not Zariski-dense.
Let `H_{k+1}` be the set of subgroups of `SL_3(Z)` acting on a tree without
inversions with vertex stabilizers in `H_k` and virtually solvable edge
stabilizers. Put `H = ∪_k H_k`.

Every group in `H` is coherent. If `K <= SL_3(Z)` is finitely generated and
not finitely presented, then:

- (i) `K` is Zariski-dense in `SL_3`;
- (ii) `[SL_3(Z) : K]` is infinite;
- (iii) `K` has no infinite normal virtually solvable subgroup;
- (iv) `K` is not in `H`: free products of non-dense subgroups, and amalgams
  or HNN extensions of them over unipotent or diagonalizable subgroups, are
  all coherent.

So Zaremsky Problem 3.4 has a positive answer if and only if every finitely
generated Zariski-dense subgroup of infinite index in `SL_3(Z)` outside `H`
is finitely presented.
