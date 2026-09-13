---
rg: 2
id: permutation-valued-ternary-relative-distribution
kind: claim
title: Whole-table ternary unitary correlations admit a compatible permutation-valued relative distribution
artifacts:
  - research/artifacts/hyperlinear-extreme-breakthroughs-2026-08-18.md
---

Group multiplication is intrinsically ternary:

```text
||U_g U_h-U_k||_2^2 = 2-2 Re tau(U_h* U_g* U_k).
```

**Target.** For every finite regular-trace unitary table, construct a
dimension-free contextual joint object for its triples that controls these
cubic traces, is compatible on overlapping associativity squares, and decodes
to a **common latent family of partial bijections or multiplicative
bistochastic kernels**. Pairwise relative distributions must appear as
marginals, but separate pairwise couplings are not enough.

The classical alphabet is load-bearing. Scalar roots of unity commute and
would only round an abelianized shadow of the table. The endpoint must be
permutation-valued / quantum-magic / common-latent, not merely scalar phase
rounding. The source artifact proves separately that finite-order spectral
normalization can be done dimension-free if an NC-CSP implementation needs a
finite operator alphabet.

## Attempts

- **Apply an NC-2-CSP relative distribution independently to each pair.** The
  pairwise laws need not agree around an associativity square and therefore do
  not define one multiplication table.
- **Extend to a scalar three-variable phase law.** Even a perfect theorem of
  that form lands in commuting scalars, not in nonabelian finite actions.
- **Use pair-groupoid coordinates `X_{a,b}=U_a*U_b`.** This rewrites many
  relations as pairwise closeness and gives the exact flat law
  `X_{a,b}X_{b,c}=X_{a,c}`, but enforcing that flatness around triangles is
  itself the missing contextual/ternary compatibility. It is a coordinate
  system, not a solution.
- **Build the contextual object from joint trace moments, by an argument valid
  for every tracial model.**  Cannot work (§3 of
  `research/artifacts/q34-rounding-routes-2026-09-12.md`).
  - The regular representation of the group of
    `finitely-presented-nonsofic-group-exists` is an exact regular-trace table
    on every window, with cubic traces `tau(U_h^* U_g^* U_k) = 1[gh = k]`.
  - Such a construction would produce the object there.  Decoding it would
    make that group sofic (`markov-sofic-equals-sofic`).
  - So the construction must read the finite-dimensional microstate, at a step
    with no analogue in a tracial algebra.
