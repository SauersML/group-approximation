---
rg: 2
id: stw40-trace-simplex-boundary-is-topologically-amenable
kind: claim
title: The boundary forced inside an XL trace simplex is an amenable boundary
distinct_from:
  stw40-trace-simplex-contains-a-nontrivial-boundary: that extracts minimality and strong proximality from affine convex dynamics; the present theorem adds topological amenability inherited from the original C-star action.
---

Let `G` be countable and nonamenable, and let `alpha:G acts on A` be an
amenable action on a unital separable nuclear C-star algebra with nonempty
trace simplex.  The nontrivial minimal strongly proximal compact subsystem

```text
X subset T(A)
```

obtained in `stw40-trace-simplex-contains-a-nontrivial-boundary` carries a
topologically amenable `G`-action.  Thus `X` is an amenable `G`-boundary.

Indeed amenability of a C-star action implies topological amenability of the
induced action on the state space.  The trace simplex is a closed invariant
subspace of the state space, and `X` is a closed invariant subspace of
`T(A)`; restricting the continuous probability-valued amenability witnesses
twice proves the claim.

Consequently every XL witness must realize an amenable boundary inside its
trace dynamics.  Combined with the compact commutative construction, this
isolates the open step precisely: replace the nonsimple algebra `C(X)` of an
amenable boundary by a unital stably finite classifiable realization without
destroying amenability of the C-star action.
