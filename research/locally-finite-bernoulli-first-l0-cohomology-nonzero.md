---
rg: 2
id: locally-finite-bernoulli-first-l0-cohomology-nonzero
kind: claim
title: Locally finite groups have nonvanishing first L0-cohomology on Bernoulli actions
artifacts:
  - research/artifacts/km-lattice-cohomology-and-lp-fork-2026-08-23.md
distinct_from:
  km-some-ergodic-action-has-nonzero-l0-second-cohomology: that is the open degree-TWO question for the whole lattice; this is a proved degree-ONE theorem for its locally finite subgroups, feeding that question's E2^(1,1) entry.
  km-l0-cohomology-is-the-49-orbit-invariants-complex: that reduces the lattice's low-degree cohomology to a finite complex; this computes (nonvanishing of) one kind of input entry appearing after the column analysis.
---

**THEOREM (established; proof in
`locally-finite-bernoulli-lim1-proof`).**  Let `G` be a countable
infinite locally finite group acting freely on a countable index set
`I` with infinitely many orbits, and let `Y = ([0,1]^I, product
measure)` with the induced p.m.p. action.  Then

```text
H^1(G, L^0(Y, R)) != 0,
```

exhibited by explicit cocycles; equivalently, the tower of invariant
subspaces `{L^0(Y)^(G_n)}` along any exhausting chain of finite
subgroups has nonvanishing algebraic `lim^1`.  The construction is
equivariant enough that the nonzero class can be chosen invariant
under any prescribed finite group normalizing the chain.

**Corollary (the lattice's negative parabolics).**  For `Lambda =
Lambda_(2,4,6)(q)` acting on its Bernoulli shift `Y = [0,1]^Lambda`,
EVERY proper negative standard parabolic `P_K^-` (in particular
`B_- = T . U_-` and the three rank-one `P_k^-`) is locally finite
(finite Levi extension of the locally finite unipotent part), acts
freely with infinitely many orbits, and hence has

```text
H^1(P_K^-, L^0(Y, R)) != 0.
```

This makes every group entry at J-line degree one in the
`km-some-ergodic-action-has-nonzero-l0-second-cohomology` double
complex NONZERO; what remains open for the lattice's `H^2` is only
the stable-element linear algebra of the K-direction (see that
node's Attempts).
