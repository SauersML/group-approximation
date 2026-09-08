---
rg: 2
id: ck-quotient-corner-has-infinite-bi-index
kind: claim
title: Every nontrivial quotient of the direct CK envelope retains infinite simple-core bi-index
distinct_from:
  direct-ck-corner-core-has-infinite-bi-index: that uses literal matrix entries before quotienting; this proves a quotient-ring lower bound for every proper normal quotient and transfers the obstruction to marked covers and finite stabilizer enlargements.
  ck-envelope-simple-core-has-finite-bi-index: that remains an existential question over other envelopes and embeddings; this excludes the entire family retaining the canonical corner through the specified quotient and cover maps.
artifacts:
  - research/artifacts/ck-quotient-and-cover-bi-index-obstruction-2026-09-08.md
  - research/artifacts/ck-quotient-bi-index-cairn-validation-2026-09-08.json
---

Let `S` be infinite simple, `Z[S]` a unital subring of `U`, and
`1-s_0` full in `U` for some `1!=s_0 in S`. Suppose the corner subgroup
`D={diag(s,1,...,1):s in S}` lies in `Gamma=EL_n(U)`, `n>=3`.

For every proper normal subgroup `N` of `Gamma`, put `Q=Gamma/N`,
`D_N=q(D)`, and `I=lev(N)`. Then `D_N` is isomorphic to `S`, and

```text
U/I -> D_N \ Q / D_N,
a+I |-> D_N q(e_23(a)) D_N
```

is injective. The ring `U/I` is infinite, so the bi-index is infinite.

This also implies infinite bi-index:

1. in any overgroup of `Q`, for the same embedded `D_N`;
2. for `T<=P` whenever a surjection `P->Q` maps `T` onto `D_N`;
3. after any finite-index enlargement of a stabilizer already covered by
   either of the preceding statements or the quotient statement.

In particular, neither a nontrivial quotient of the direct CK envelope nor
a marked cover of one repairs its canonical simple-core coset action.
This includes the original CK cover when its marked subgroup maps to the
corner copy. Arbitrary different stabilizers or embeddings remain outside
the statement. No claim about simplicity or finite presentability of `Q`
is made.

DERIVATION
[[ck-quotient-corner-bi-index-proof]]
