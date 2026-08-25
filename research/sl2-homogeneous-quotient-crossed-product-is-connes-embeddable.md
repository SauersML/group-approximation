---
rg: 2
id: sl2-homogeneous-quotient-crossed-product-is-connes-embeddable
kind: claim
title: The amalgamated free product of two profinite crossed products of SL2(Z) over a cocompact tree quotient is Connes embeddable
invalidates:
  - non-hyperlinear-from-relative-commutant-collapse
  - nonhyperlinear-coset-wreath-from-commutant-collapse
  - sl2-amalgamated-free-exclusion-from-collapse
  - rcc-from-spherical-leak-exclusion
  - exact-leak-refuted-by-projective-transfer
  - projective-transfer-proves-canonical-iwahori-transfer
  - sl3-coset-lamp-collapses-from-projective-transfer
distinct_from:
  sl3-homogeneous-quotient-crossed-product-is-connes-embeddable: that is the higher-rank instance with a single gluing unitary and property (T); this is the rank-one instance, an amalgamated free product of two profinite algebras over a finite-index subalgebra, where the lattice is a free group and the quotient a finite Ramanujan graph.
  relative-commutant-collapse-for-sl2-pair: that is the collapse statement in every matrix ultraproduct; this is the embeddability of one explicit crossed product whose truth refutes it.
  coset-wreath-is-hyperlinear: that is a wreath group over the SL_3 pair with a weakly mixing lamp algebra; this is a rank-one crossed product of a compact quotient with profinite pieces and no lamps.
---

**OPEN (two-sided).**  Let `Lambda' < SL_2(Q_2)` be a torsion-free cocompact
lattice (a free group; e.g. a unit group of a definite quaternion order split
at `2`) with at least two `SL_2(Z_2)`-orbits on `X = SL_2(Q_2)/Lambda'`, so
that `K \ SL_2(Q_2)/Lambda'` is a finite `3`-regular graph.  Claim: the
II_1 factor

```text
M_2 = L^infinity(X) rtimes SL_2(Z[1/2])
    = (L^infinity(X) rtimes SL_2(Z)) *_(L^infinity(X) rtimes D) (L^infinity(X) rtimes g SL_2(Z) g^-1),
    g = diag(2,1),                                                    (S2H1)
```

is Connes embeddable.  Both free factors are Connes-embeddable profinite
crossed products (`(HQ4)` of
`homogeneous-quotient-ce-refutes-arithmetic-commutant-collapse`), the
amalgam is a finite-index subalgebra of each, and `X` is a Cantor set on
which `SL_2(Z)` and its conjugate act profinitely through two adjacent
maximal compact subgroups of `SL_2(Q_2)`.

**Stakes both ways.**  By the same theorem, `(S2H1)` embeddable refutes
`relative-commutant-collapse-for-sl2-pair`,
`projective-commutant-transfer-for-arithmetic-pair` and
`no-spherical-leak-in-matrix-ultraproducts`, hence the `invalidates` keys.
A proof of the collapse must instead show that this amalgamated free
product of two embeddable algebras over a finite-index base is not
embeddable, which would answer Gao--Junge's amalgamated-free-product
permanence question negatively in its finite-index form.  Neither outcome
produces a nonhyperlinear group directly.

## Attempts

- **Brown--Dykema--Jung.**  Needs the base hyperfinite; here the base
  `L^infinity(X) rtimes D` (`D = C cap g C g^-1`, index `3`) contains `L(D)`, which has
  free subgroups, so it is not amenable.  The finite-index hypothesis is
  exactly what their argument does not use.
- **Permutation models from the finite graph.**  As in the rank-two case,
  `K_m \ SL_2(Q_2)/Lambda'` carries only Hecke correspondences; the leak
  `U` is a `+-1` labelling of the finite graph's vertices moved by
  `e_21(1/2)`, and any Cartan model would force it to be nearly invariant.
  The action is expected nonsofic by the Kun--Thom mechanism (here the pair
  `SL_2(Z) < SL_2(Z[1/2])` has only relative property (T) inputs, so even
  that is not proved), and nonsoficity of the action would not decide
  `(S2H1)`.
- **Tree structure.**  `SL_2(Z[1/2])` acts on the `3`-regular tree with
  vertex stabilisers conjugate to `SL_2(Z)`; `M_2` is the crossed product of
  the quotient of the p-adic group by a lattice acting freely on the same
  tree.  A Bass--Serre-type decomposition of microstates along the tree,
  gluing congruence microstates of adjacent stabilisers over the
  finite-index intersection `D`, is the natural constructive
  approach; the obstruction is that the two stabilisers' congruence
  filtrations of `X` are different (adjacent maximal compacts are not
  commensurable in a way that respects the `C`-orbit labels), so no
  common finite level exists at which both act.  This is now isolated and
  proved as
  `homogeneous-k-orbit-factor-has-no-finite-a-refinement`:
  no finite equivariant refinement of the `K`-orbit label exists.  The theorem
  only excludes exact Cartan/common-level models; compatible non-Cartan
  tracial-ultraproduct embeddings remain the live constructive possibility.
  Deferred.
- **Finite index does not promote the exact-level obstruction.**
  `iwahori-index-data-does-not-block-ultraproduct-gluing`
  writes each vertex algebra trace-preservingly in `M_3(B)` and identifies
  the residual as stable unitary equivalence of the two induced embeddings
  of `B` after reindexing and amplification.  The centers form the finite
  edge--vertex incidence diagram and admit an exact common matrix model; the
  two local index-three Jones towers are isomorphic.  Thus trace, center,
  Pimsner--Popa, and separate local standard-invariant data cannot turn
  `homogeneous-k-orbit-factor-has-no-finite-a-refinement` into a non-Cartan
  ultraproduct no-go.  The remaining datum is global cycle holonomy, namely
  the free lattice's right-translation return maps in `(DT2)`.
- **A common finite normal edge core does not exist.**  One might try to
  replace the index-three edge by a further finite-index subgroup normal in
  both vertices, turning both faces into finite-group extensions of one
  shared base.  `iwahori-edge-has-no-common-finite-index-normal-core` rules
  this out: such a core would be normal in all of `SL_2(Z[1/2])`, and the
  S-arithmetic normal-subgroup theorem would contradict the infinite index
  of the vertex group.  Thus finite-depth/Morita reduction does not bypass
  the nonamenable amalgam; ultraproduct-level compatibility remains open.
- **The stable crossed-product residual is exactly joint spatialization.**
  `free-lattice-ce-is-joint-ultrapower-spatialization` compresses `(DT2)` to
  one finite corner `N_q` and proves that `(S2H1)` is Connes embeddable iff
  there is a single embedding `pi:N_q->R^omega` in which all free-generator
  return automorphisms become inner simultaneously.  Every one-generator
  condition holds separately by amenable crossed-product permanence.  Thus
  neither a local return nor a separate choice of vertex microstates can
  decide the problem; the live datum is the common embedding for the entire
  free-lattice packet.
