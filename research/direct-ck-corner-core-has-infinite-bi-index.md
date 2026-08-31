---
rg: 2
id: direct-ck-corner-core-has-infinite-bi-index
kind: claim
title: The canonical simple core has infinite bi-index in the direct CK elementary envelope
distinct_from:
  ck-envelope-simple-core-has-finite-bi-index: that asks whether some normal-generator envelope can be arranged to give the core finite bi-index; this proves that the explicit direct elementary envelope supplied by the universal-sandwich improvement cannot be that arrangement.
  simple-core-bi-index-counts-coset-action-pair-orbits: that identifies pair-orbits with double cosets abstractly; this supplies an explicit infinite family of those double cosets in the direct matrix construction.
artifacts:
  - research/artifacts/boone-higman-direct-ck-double-coset-no-go-2026-08-31.md
---

Let `U` be a unital ring, let `n >= 3`, and let `H <= U^x` be a subgroup
whose upper-left corner copy

```text
d(H) = { diag(h,1,...,1) : h in H }
```

lies in `EL_n(U)`.  Then the map

```text
U  -->  d(H) \ EL_n(U) / d(H),
a  |-->  d(H) e_23(a) d(H)
```

is injective.  In particular, if `U` is infinite, `d(H)` has infinite
bi-index in `EL_n(U)`.

Apply this to the direct Chatterji--Kassabov envelope

```text
Gamma = EL_4(U),
U = Z[Gtilde]<p,q>/(p(1-g)q-1).
```

The input simple core `S <= [Gtilde,Gtilde]` enters `Gamma` by the
upper-left corner embedding used in the CK construction, and `U` is infinite
because `Z[Gtilde] -> U` is injective.  Hence

```text
| S \ Gamma / S | >= |U|,
```

so the coset action `Gamma` on `Gamma/S` has infinitely many pair-orbits.
The direct universal-sandwich envelope therefore cannot close the
finite-bi-index/twisted-Brin--Thompson route.

DERIVATION
[[direct-ck-corner-core-infinite-bi-index-proof]]

This does not refute the existential claim that a *different* envelope or a
different embedding might have finite bi-index, and it does not touch the
maximal-kernel or action-image routes.
