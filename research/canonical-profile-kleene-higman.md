---
rg: 2
id: canonical-profile-kleene-higman
kind: claim
title: Reverse Kleene needs only qualitative group-algebra collapse on canonical microstates
artifacts:
  - research/artifacts/meta-recursive-qca-audit-2026-08-22.md
distinct_from:
  threshold-free-reverse-kleene-higman-diagonal: that asks for group-word death in every tracial matrix-ultraproduct homomorphism; this asks only for canonical-delta microstate collapse and permits a rational group-algebra mark.
  group-algebra-mark-reverse-kleene-collapse: that uses a finite presentation and finitely specified trace side tests; this permits a uniformly recursively enumerable presentation and a wholly qualitative canonical-profile hypothesis before effective Higman embedding.
  unconditional-bcs-ultraproduct-decoder-forces-ce: that obstructs decoding the trivial homomorphism; canonical-profile microstates exclude that homomorphism for every nontrivial group and require no unconditional decoder.
---

Suppose a total computable compiler sends each machine index `e` to a finite
alphabet `S_e`, a uniformly recursively enumerable relator stream `R_e`, and a
finite rational group-algebra expression `p_e in Q[F(S_e)]`. Put
`Gamma_e=<S_e|R_e>`. Assume

```text
e halts     => p_e != 0 in Q[Gamma_e],                       (CPK1)
e nonhalts  => every canonical-profile microstate sequence
               for Gamma_e has ||p_e(U_n)||_2 -> 0.          (CPK2)
```

Then one can effectively construct a finitely presented non-hyperlinear group.
The fixed-point program never reads a relator-defect threshold, moment window,
trace tolerance, decoder modulus, matrix dimension, or runtime bound.

This is strictly weaker than hyperlinear-radical membership: exact
finite-dimensional representations with noncanonical characters may detect
`p_e` without affecting `(CPK2)`.
