---
rg: 2
id: finite-swap-conjugate-moments-do-not-fold-arithmetic-double
kind: claim
title: Every finite block-swap character table has an exact finite regular model
distinct_from:
  finite-spherical-moments-do-not-fold-regular-double: that constructs atomic quadratures for finite spherical Hecke moments; this treats all finite joint moments of the swap involution and its arithmetic conjugates, including their half-projections
  sl3-regular-double-bass-serre-rigidity-firewall: that gives one exact infinite-dimensional nonfolded swap; this proves finite-dimensional exact realizability of every finite swap-only moment window
---

Use the binary coset-wreath form

```text
E=( *_(x in A/C) C_(2,x) ) rtimes A
```

from `arithmetic-double-swap-extension-is-binary-coset-wreath`, and denote
the generator of the factor at `x` by `s_x`.  Let `X_0` be any finite set of
cosets and let `W` be any finite set of nontrivial reduced words in the
letters `{s_x:x in X_0}`.  There is a finite-dimensional exact unitary model
such that

```text
tr(s_x)=0,
tr(v)=0 for every v in W,                                (FSM2)
```

exactly as in the canonical character of `E`.

Indeed the finite free product

```text
K_(X_0)=*_(x in X_0) C_(2,x)
```

is virtually free and residually finite.  Choose one finite quotient which
keeps every word in `W` and every `s_x` nontrivial.  Its regular
representation has trace zero on all those elements, proving `(FSM2)`.

Consequently every finite joint moment table of the half-projections

```text
P_x=(1+s_x)/2                                             (FSM3)
```

has an exact finite-dimensional model: expand the finitely many requested
projection monomials as linear combinations of lamp words and include every
nontrivial word in their supports in `W`.  The model can match the moments
exactly, not merely approximately.

Thus canonical character data of the block swap, its spectrum, any finite
family of arithmetic conjugates, and all finite projection-overlap moments
among them cannot force the fold `s_x=s_y`.  A proof of
`sl3-regular-arithmetic-double-fold-mark-collapse` must use the joint
extension of these swaps by the approximate arithmetic matrices and the
finite presentation of `A`; it cannot be a swap-character or projection
moment argument alone.  This is the precise lamp-side analogue of the
spherical quadrature firewall.
