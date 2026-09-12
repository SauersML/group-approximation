---
rg: 2
id: finite-subgroup-data-cannot-force-defect-submultiplicativity
kind: claim
title: Relations inside finite subgroups and conjugation-invariant ranks are realized with independent cylinder defects of rank three eighths
distinct_from:
  unitriangular-data-cannot-assemble-corner-leavitt-families: that shows unitriangular relations and conjugation-invariant ranks cannot assemble a corner Leavitt family; this covers all finite-subgroup data, including Weyl elements, halving sheets, prefix doubling, the swap and conjugation by torus units or compressors, and targets the multiplicative deficit rather than a Cuntz family.
  fd-represented-coefficients-violate-two-root-identities: that gives honest models over finitely represented coefficient rings violating the two-root identity; this is a single conjugation-invariant rank assignment on all finite-subgroup algebras of the Leavitt unit group, with exactly multiplicative disjoint defects.
  leavitt-disjoint-cylinder-defects-strictly-submultiplicative: that is the open strict deficit; this shows no argument from finite-subgroup data and conjugation equalities alone proves it.
  locally-finite-hnn-data-allow-independent-cylinder-defects: that gives a fixed-point-free rank model on HNN data over a locally finite subgroup, covering single conjugations as operators; this is the simpler regular assignment on all finite-subgroup algebras, which fixes ranks of finite-subgroup elements and their conjugates but builds no model on the HNN group.
  sofic-subgroups-carry-rank-models-violating-two-root-identity: that builds a rank model violating the two-root identity on one sofic subgroup, used by w4-r4-orth to realize the halving relations and the swap for one configuration; this is one assignment on all finite-subgroup algebras simultaneously, invariant under conjugation by every unit, which covers Weyl elements over F_2, iterated sheets and compressor or torus conjugations as well.
artifacts:
  - research/artifacts/cylinder-commutant-independence-and-weyl-firewall-2026-09-12.md
---

**ESTABLISHED** (route `finite-subgroup-regular-assignment-firewall-proof`; artifact Section 3;
independent re-derivation requested from `w4-vf-gate`).

**Statement.** Let `R^x = L_(F_2)(1,2)^x`. For `alpha` in `F_2[R^x]` whose support generates a finite
subgroup `K`, put `rk_reg(alpha) = dim(alpha F_2[K]) / |K|`. Then:
* `rk_reg` is well defined, and on the group algebra of every locally finite subgroup it is the rank
  function of a rank model over `F_2`, fixed-point-free when the subgroup is infinite;
* it is invariant under conjugation by every unit of `R^x`;
* for disjoint proper cylinders `A_1, ..., A_k`, `rk_reg(D_(A_1) ... D_(A_k)) = (3/8)^k`.

**Consequence.** No inequality `rk(D_A D_B) <= theta rk(D_A) rk(D_B)` with `theta < 1` follows from rank
calculus on finite-subgroup algebras, group relations inside finite subgroups, and rank equalities
between conjugates. Weyl elements over `F_2`, the halving sheets `x_12(e_0) x_12(e_1)`, the prefix
doubling that makes the doubled defect conjugate to a single defect, the swap of two cylinders, and
conjugation by torus units or compressors are all inputs of this kind.

**What a proof must use instead.** `sigma` on a subgroup that is not locally finite, entering as factors
in an operator identity: opposite root elements with non-constant coefficients generating an infinite
dihedral group, or torus units and prefix replacements of infinite order inside products with defects.
Or a global input such as corner locality turned into an upper bound. The isometry-coefficient root
elements `n_12(t_i)`, `n_23(s_j)` and the block root groups `x_12(r)` do not qualify: they generate
locally finite groups with any finite configuration, so this claim covers them. (The first landing,
01aa418e41, named the isometry-coefficient root elements as a way out; that was wrong, since they lie in
the locally finite `UT_3(R)`.)

## Attempts

- Established, not open. The proof is the free-module computation in `F_2[D_8]` and
  `F_2[D_8 x D_8]` plus conjugation invariance of regular ranks.
