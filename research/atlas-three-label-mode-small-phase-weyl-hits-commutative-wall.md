---
rg: 2
id: atlas-three-label-mode-small-phase-weyl-hits-commutative-wall
kind: claim
title: Standard clock-shift coefficients on the three-label Atlas slice converge to the commutative wall
invalidates:
  - atlas-three-label-mode-weyl-pair-model
distinct_from:
  leavitt-regular-atlas-block-monomial-gap: that gives the general bounded-complexity and asymptotically-commuting coefficient fences; this evaluates the first full-coefficient three-label construction, including its exact literal moment limit, and places it behind that fence.
  atlas-outer-involution-two-sector-collapses-to-one-unitary: that leaves a literally commutative one-unitary algebra after gauge; here every finite coefficient algebra is the full growing matrix algebra, but its fixed word moments and commutators asymptotically become commutative.
  atlas-fixed-formal-toeplitz-microstates-promote: that treats fixed-width formal triangular symbols in binary rank; this treats growing complex Weyl irreducibles in normalized Hilbert--Schmidt norm.
---

**ESTABLISHED SCOPED NO-GO.**  Let `S_r,D_r` be the standard clock and
shift pair in `(TWM0)`, and let `U_r` be the three-label relative unitary
from `(TLM3)` with `Z_1=S_r`, `Z_2=D_r`.  Then

```text
liminf_(r->infinity)
 max_(s in bar_S) ||pi_(U_r)(s)-I||_2 > 0.            (TWM1)
```

More explicitly, every fixed coefficient word reduces to

```text
m(S_r,D_r)=zeta_r^(Area(m)) S_r^(a(m)) D_r^(b(m)),    (TWM2)
```

where `a(m),b(m),Area(m)` are fixed integers.  For `r` larger than the word
length,

```text
tr_r(m(S_r,D_r))
 =0                         if (a(m),b(m)) != (0,0),
 =zeta_r^(Area(m))          if (a(m),b(m)) = (0,0).   (TWM3)
```

Hence these moments converge to

```text
1_({a(m)=0,b(m)=0}),                                   (TWM4)
```

the joint moments of two commuting Haar coordinate unitaries on the
two-torus.  Substitution in `(TLM7)` gives the exact limiting defect of every
literal Atlas word on this ansatz.

At the operator level,

```text
||S_r D_r-D_r S_r||_2=|zeta_r-1| -> 0.                (TWM5)
```

All block coefficients of `U_r` are fixed scalar linear combinations of
`I,S_r,D_r`; commutators among their real and imaginary parts are therefore
`O(|zeta_r-1|)`.  If a subsequence made the Atlas packet defect tend to zero,
it would contradict `(BMG3)` of
`leavitt-regular-atlas-block-monomial-gap`, which requires one fixed
block-coefficient commutator to retain order-one normalized-HS norm in every
certificate sequence.  This proves `(TWM1)`.

The conclusion does not follow merely from finite-stage fullness:
`C*(S_r,D_r)=M_r(C)` at every `r`.  It is the vanishing commutation phase,
visible in both `(TWM3)` and `(TWM5)`, that makes this full-coefficient family
asymptotically abelian and unusable.

DERIVATION
atlas-three-label-mode-weyl-wall-proof
