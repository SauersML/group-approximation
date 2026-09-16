---
rg: 2
id: sl3z-normal-f2-subgroups-have-virtually-cyclic-quotients
kind: claim
title: If a subgroup of SL_3(Z) has a normal subgroup isomorphic to F_2, the quotient is finite or virtually infinite cyclic and the subgroup is finitely presented
distinct_from:
  sl3z-infinite-index-normal-fibers-force-zariski-density: that claim forces a non-solvable finitely generated normal fibre to be Zariski dense and thin; this one bounds the quotient by a normal F_2, whatever its Zariski closure
  sl3z-normal-subgroup-class-stabilizers-are-polycyclic: that is the general stabilizer lemma for any normal subgroup; this is its consequence for a normal subgroup isomorphic to F_2, using that every automorphism of F_2 preserves the commutator class up to inversion
  sl3z-products-of-infinite-subgroups-are-polycyclic: that forbids commuting pairs such as F_2 x Z; this forbids every F_2-by-(not virtually cyclic) subgroup, including the semidirect products F_2 x| F_m with m >= 2, which contain no F_2 x Z
artifacts:
  - research/artifacts/sl3z-normal-f2-obstruction-2026-09-16.md
---

Let `G <= SL_3(Z)` and let `N ◁ G` with `N ≅ F_2`. Then:

1. `C_G(N)` is finite, and the monodromy `G/N -> Out(N) ≅ GL_2(Z)` has
   finite kernel.
2. `G/N` is finite or has an infinite cyclic subgroup of finite index.
3. Every element of infinite order in `G/N` has monodromy of infinite order.
4. `G` is finitely presented. Either `G` is virtually `F_2`, or `G` has a
   finite-index subgroup `F_2 x|_φ Z` with `φ` of infinite order in
   `Out(F_2)`.

**Corollaries** (artifact, Section 5).

- `SL_3(Z)` contains no extension `1 -> F_2 -> E -> Q -> 1` with `Q` not
  virtually cyclic. In particular it contains no `F_2 x| F_m` with `m >= 2`,
  no `F_2 x| Z^2`, and no `F_2`-by-surface group. This refutes
  `sl3z-contains-f2-by-free-subgroup`.
- No subgroup of `SL_3(Z)` with a normal `F_2` is a witness of
  incoherence.
- If `N ◁ G <= SL_3(Z)` and `A <= N` with `A ≅ F_2`, then the stabilizer of the
  `N`-conjugacy class of `A` in `G/N` is virtually cyclic.

**Effect on Serre's question.** The Kropholler–Walsh incoherence theorem
for finite-index subgroups of `F_2 x| F_n` (arXiv:1910.09601, abstract) has no
instance inside `SL_3(Z)`; see the dead route
`sl3z-incoherent-via-f2-by-free-subgroup`. The free-by-free candidates for
`sl3z-contains-cd2-euler-positive-fibered-subgroup` must have fibre rank at
least 3.

Proposition A does not assert that any `F_2 x|_φ Z` embeds in `SL_3(Z)`.
Whether some Long–Reid specialization of the figure-eight knot group is
faithful was not settled here.
