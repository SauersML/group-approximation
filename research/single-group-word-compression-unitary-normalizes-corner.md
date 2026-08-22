---
rg: 2
id: single-group-word-compression-unitary-normalizes-corner
kind: claim
title: A single compressed group word is a corner unitary only when it normalizes the corner
distinct_from:
  irreducible-finite-packet-normalizer-words-scalarize: that assumes normalization and classifies multiplicity words; this proves normalization from corner unitarity of one compressed group element.
---

# A single compressed group word is a corner unitary only when it normalizes the corner

ESTABLISHED. Let `q` be a nonzero projection in a finite tracial von Neumann
algebra and let `w` be a unitary. If

```text
x=q w q
```

is unitary relative to the corner unit `q`, then

```text
w q w^*=q.                                                (SC1)
```

Indeed `x^*x=q` says `q p q=q` for the projection `p=w^*qw`. Hence
`q<=p`. Traciality gives `tau(p)=tau(q)`, and faithfulness gives `p=q`.

In particular, for any group `Gamma`, algebraic corner projection
`q in C[Gamma]`, and group word `w in Gamma`, the equality making `qwq` a
unitary in `qC[Gamma]q` forces `w` to stabilize `q` in the canonical finite
group von Neumann algebra, hence algebraically. A single stable-letter word
cannot be the desired nonnormal additive multi-path corner unitary.

For the smallest Pauli packet `K=D_8`, with central involution `z` and
two-dimensional type projection `q=(1-z)/2`, a free stable letter gives

```text
q w q=(w-z w-w z+z w z)/4.                               (SC2)
```

Although `(SC2)` has four group-ring terms, it is not a corner unitary. In
the free product trace its normalized corner squared norm is exactly `1/2`:
the projections `q` and `w^*qw` are free and both have trace `1/2`. Imposing
unitarity collapses `(SC2)` to the normalizer case by `(SC1)`.

