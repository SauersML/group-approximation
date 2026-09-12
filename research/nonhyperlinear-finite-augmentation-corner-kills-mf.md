---
rg: 2
id: nonhyperlinear-finite-augmentation-corner-kills-mf
kind: claim
title: A no-CE algebra in any finite-subgroup augmentation corner forces the whole subgroup into the MF radical
distinct_from:
  nonhyperlinear-normal-augmentation-corner-kills-mf: that assumes the finite subgroup is normal; this removes that unnecessary hypothesis by compressing only the algebra images.
  agent-leavitt-not-torsion-corner-noce-forces-mf-radical: that authenticates a cyclic finite subgroup using its full torsion spectral projection; this allows any finite subgroup and is useful for full affine-field matrix packets.
  nonce-bcs-unital-algebraic-corner-map-forces-nonhyperlinear: that uses the canonical trace to exclude hyperlinearity; this makes every norm-corona representation kill the full augmentation complement and hence the finite subgroup, even at vanishing support density.
artifacts:
  - research/artifacts/nonnormal-finite-augmentation-corner-endgame-2026-09-08.md
---

Let `B` be a unital star algebra with no Connes-embeddable tracial
state, let `G` be countable, and let `K<=G` be finite. Put

```text
q_K=1-|K|^-1 sum_(k in K)k.
```

If there is a unital star homomorphism

```text
B -> q_K C[G]q_K,             1 |-> q_K,
```

then `K<=Rad_MF(G)`. Thus nontrivial `K` proves that `G` is not
MF. Normality of `K`, centrality of `q_K`, a lower bound on matrix
support proportions, and property `(T)` are all unnecessary.

More generally, for any group-ring projection `q`, a unital map
`B->qC[G]q` forces every norm-corona homomorphism to annihilate `q`.
Every nonzero corner of a norm matrix corona maps unitally to a
tracial matrix ultraproduct after normalizing by its own coordinate
ranks. Composing the algebra map would otherwise give a CE trace.

DERIVATION
nonnormal-augmentation-corner-intrinsic-rank-proof
