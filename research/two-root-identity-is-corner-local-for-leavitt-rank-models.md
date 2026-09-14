---
rg: 2
id: two-root-identity-is-corner-local-for-leavitt-rank-models
kind: claim
title: A characteristic-two rank model of the binary Leavitt unit group is trivial exactly when the two-root identity holds on any one cylinder corner
distinct_from:
  rank-models-of-el3-satisfy-the-two-root-identities: that is the open assertion that every rank model satisfies the identity on the unit pair; this is the established per-model equivalence between triviality, the identity on the unit pair, and the identity on the root pair of any single cylinder corner.
  matrix-unit-rank-models-extract-ring-rank-models: that extracts a ring rank model from a matrix-unit model; this combines that extraction with corner embeddings and simplicity to localize the identity to an arbitrary cylinder.
  shifted-root-pair-conjugates-to-idempotent-root-pair: that is a conjugacy between the shifted pair and the e_0 corner pair, with an invariant separating both from the unit pair; this is a triviality criterion per model, which through that conjugacy also makes the shifted pair a test of triviality.
artifacts:
  - research/artifacts/two-root-identity-nonsofic-mechanism-2026-09-12.md
---

**ESTABLISHED** (proof in the artifact, Section 2). Let `R = L_(F_2)(1,2)` and
`R^x = EL_3(R)` through the code `(0, 10, 11)`. Let `sigma` be a homomorphism from `R^x` into
the units of a rank ultraproduct over a field of characteristic two. For a prefix `P` put
`iota_P(g) = S[P] g T[P] + (1 - S[P]T[P])`, an injective group endomorphism. Then the following
are equivalent:

1. `sigma` is trivial;
2. `(sigma(x_23(1)) - 1)(sigma(x_12(1)) - 1) = 0`;
3. `(sigma(iota_P(x_23(1))) - 1)(sigma(iota_P(x_12(1))) - 1) = 0`.

So a nontrivial model violates the identity on the unit pair and on the root pair of every
cylinder corner simultaneously. A proof of `rank-models-of-el3-satisfy-the-two-root-identities`
may test the identity on a pair supported on a single cylinder. One such cylinder is `[1000]`,
whose units commute with the Kazhdan subgroup of the nine-leaf configuration.
