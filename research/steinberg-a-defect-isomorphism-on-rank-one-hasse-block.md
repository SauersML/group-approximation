---
rg: 2
id: steinberg-a-defect-isomorphism-on-rank-one-hasse-block
kind: claim
title: The A defect is invertible on the interior rank-one Hasse block
artifacts:
  - research/steinberg-rank-one-hasse-block-proof.md
distinct_from:
  steinberg-standard-augmentation-filtration-firewall: that rules out a standard global filtration; this extracts a positive dense block isomorphism from the same exact coefficients.
  steinberg-x-plus-incidence-dual-is-surjective: this proves one pivot block is invertible but does not control the Schur complement fed by all other quotient monomials.
---

**ESTABLISHED.**  For every odd `p>=5`, in the quotient of chord functions
by endpoint potentials let

```text
S=span{[a^i c]: 2<=i<=p-2}.
```

The `A` defect `(1-q^(-1))A^(-1)` maps `S` isomorphically to `S` after
normal-form projection.  Its matrix is dense rather than triangular, but
has zero kernel by a translation functional equation.  The projected `B`
defect is diagonal on the same source block.  Consequently the projection
of the complete `X^*` row to `S` is one explicit `(p-3)` square matrix; its
invertibility is the next finite Schur pivot required by the direct block
Bezout route.

DERIVATION
steinberg-rank-one-hasse-block-proof
