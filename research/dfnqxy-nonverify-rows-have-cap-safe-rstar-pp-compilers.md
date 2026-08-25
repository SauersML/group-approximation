---
rg: 2
id: dfnqxy-nonverify-rows-have-cap-safe-rstar-pp-compilers
kind: claim
title: Every non-Verify DFNQXY source row has a uniform cap-safe R-star pp compiler
distinct_from:
  dfnqxy-answer-reduction-does-not-preserve-affine-safe-support: that proves the non-Verify predicates and their honest supports are affine-safe; this gives explicit fixed-language R-star pp gadgets whose lifted rows are automatically cap-supported.
  cm-empty-replacement-is-fano-cap-safe: that treats the final two-visible commutativity rows after subdivision; this treats the genuine source rows created by the preceding NP reduction.
  culf-mastel-rstar-two-tail-core-is-not-specified: that records that an arbitrary NP-completeness invocation does not choose a core; this replaces that invocation explicitly on all non-Verify test families and leaves only PCPP Verify gadgets unspecified.
---

**ESTABLISHED SOURCE-SPECIFIC PARTIAL COMPILER.**  In the final Hadamard
answer-reduced verifier of Dong--Fu--Natarajan--Qin--Xu--Yao, every source
predicate other than `Verify` is a finite conjunction of affine equations
over `F_2`: consistency and cross-check predicates are equalities, and the
Hadamard subset/code predicates are equalities and ternary parity equations.
For every such source context, the arbitrary NP reduction in the proof of
Culf--Mastel Part 1 may be replaced by an explicit pp gadget over

```text
R_*={x in F_2^4 : x_1+x_2+x_3+x_4=1} minus {1000}.       (DNV1)
```

The gadget has the following stronger property: in **every** exact tracial
model extending the source context, every target row is supported in the
same maximal Fano cap `x_4=1` (the pin row is a singleton inside that cap).
The construction stays inside the original abelian context algebra and
therefore preserves Connes embeddability.

Consequently, after choosing these gadgets in the Culf--Mastel reduction,
none of the genuine target rows descending from consistency, answer/proof
cross-check, or Hadamard subset/code tests contributes to the open Fano-cap
gate.  Together with `cm-empty-replacement-is-fano-cap-safe`, the only rows
still requiring source-specific profile selection are those descending from
the PCPP `Verify` predicates.

## Explicit compiler

Use two auxiliary variables `z,o`, private to the source context.  The one
row

```text
R_*(z,o,o,o)                                             (DNV2)
```

has the unique solution `(z,o)=(0,1)`: the other parity solution gives the
deleted ghost `1000`.  With these pins,

```text
R_*(u,v,w,o)       iff u+v+w=0,                          (DNV3)
R_*(u,v,z,o)       iff u=v.                              (DNV4)
```

Every tuple in `(DNV2)--(DNV4)` has fourth coordinate `1`, so every row is
contained in the fixed maximal cap `x_4=1`.  Decompose each affine equation
`sum_(j in T) x_j=b` into a chain of ternary xor gates `(DNV3)` and compare
the final partial sum with `z` or `o` using `(DNV4)`.  The projection of the
resulting pp system to the visible variables is exactly the original affine
relation.

In a perfect operator model, define every partial-sum involution as the
product of the corresponding commuting visible involutions and take `z,o`
to be the scalar pins.  This realizes the pp witnesses without enlarging the
von Neumann algebra, while `(DNV2)--(DNV4)` give cap support row by row.
Auxiliaries are private between source contexts, so the old visible overlaps
are unchanged.  Since the DFNQXY answer length is constant, the number of
rows in each gadget is uniformly bounded and the usual Culf--Mastel
classical-homomorphism and subdivision estimates retain constant soundness.
