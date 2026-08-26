---
rg: 2
id: transitive-product-socle-intermediate-is-an-endpoint
kind: claim
title: A transitive independently normalized product-socle intermediate is one endpoint
artifacts:
  - research/transitive-product-socle-intermediate-proof.md
distinct_from:
  scalable-socle-normalizer-reservoir-dichotomy: that asks for a dimension-independent decoding and perturbation theorem for an approximate matrix-coordinate support; this proves the exact finite-group subgroup dichotomy which that decoder is meant to expose.
  fixed-packet-normalizers-cannot-supply-the-matrix-only-pi-lock: that rules out a fixed packet tensored with an anonymous spectator; this permits an arbitrary number of socle coordinates and proves what happens once those coordinates and the intermediate subgroup have actually been authenticated.
---

**ESTABLISHED.**  Let `T` be a nonabelian simple group, let `K<T` be
nontrivial, and let `U<=Aut(T)` normalize `K`.  Assume that `K` is maximal
among the proper `U`-invariant subgroups of `T`.  Let `A<=Sym(k)` act
transitively on `{1,...,k}`.  If

```text
K^k <= E <= T^k,                                         (PSI1)
```

and `E` is invariant under the coordinatewise action of `U^k` and under the
coordinate permutations in `A`, then

```text
E=K^k    or    E=T^k.                                   (PSI2)
```

There are no diagonal or subdirect intermediate alternatives.  If every
coordinate projection of `E` is `K`, then `(PSI1)` immediately gives
`E=K^k`.  Otherwise transitivity makes every coordinate projection equal to
`T`.  In that case the subgroup of elements supported in one coordinate is
normal in `T` and contains the nontrivial group `K`; simplicity makes it the
whole coordinate copy of `T`.  Doing this in every coordinate gives
`E=T^k`.

This settles the exact algebraic half of
`scalable-socle-normalizer-reservoir-dichotomy`.  Its remaining content is
genuinely analytic and semantic: a matrix microstate must first expose the
growing product coordinates, the independently acting normalizers, and an
actual intermediate subgroup (or a stable surrogate) with a modulus uniform
in `k`.  Ordinary exactification of one fixed packet does not provide that
authentication.

The hypotheses identify the relevant sharp boundaries.  Without actor
transitivity, mixed endpoints `K^I x T^(I^c)` occur.  Without maximal
`U`-invariance, `H^k` occurs for every proper invariant intermediate
`K<H<T`.  Simplicity and the nontriviality of `K` are what eliminate
subdirect couplings after a coordinate projection becomes full.

DERIVATION
transitive-product-socle-intermediate-proof
