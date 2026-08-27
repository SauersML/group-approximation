---
rg: 2
id: congruence-cross-type-mixing-has-uniform-polar-repair
kind: claim
title: Congruence endpoint cross-type mixing has a uniform support-changing polar repair
distinct_from:
  regular-congruence-endpoint-orbit-has-uniform-selberg-retraction: that assumes equal characters and completes the averaged intertwiner to a unitary on the whole space; this permits arbitrary endpoint multiplicity mismatch and pays its unmatched support by deletion or padding.
  mixed-intertwiner-energy-transport-localization: that localizes a unitary among arbitrary representation blocks using their individual mixed spectral bottoms; this uses the uniform congruence gap and polar truncation to construct one exact large endpoint intertwiner.
  gauge-optimized-section-energy-controls-flexible-repair: that must select a compatible endpoint type from a raw exact BS core and approximate extending involution; this proves the support-changing repair after both endpoint types have already been authenticated.
---

Let `Q` be any common odd congruence quotient in the Iwahori family, and let

```text
pi,sigma:Q -> U(d)                                    (CCM1)
```

be arbitrary exact representations; their characters and irreducible
multiplicities need not agree.  For the fixed arithmetic generating set
`S`, let `kappa>0` be the uniform property-`(tau)` operator-bimodule gap,
normalized so that

```text
kappa dist_2(Z,Hom_Q(sigma,pi))^2
 <=sum_(s in S)||pi(s)Z-Z sigma(s)||_2^2.              (CCM0)
```

For every unitary `U:C^d->C^d`, put

```text
E(U)=sum_(s in S)||pi(s)U-U sigma(s)||_2^2.            (CCM2)
```

There are projections `P in sigma(Q)'`, `P' in pi(Q)'` of equal rank and an
exact partial intertwiner `V=P'VP` such that

```text
pi(g)V=V sigma(g)                         (g in Q),
tr_d(1-P)=tr_d(1-P') <=4 E(U)/kappa,
||UP-V||_2^2 <=4 E(U)/kappa.                          (CCM3)
```

After declaring `V=0` on the discarded source complement, one also has the
convenient whole-operator estimate

```text
||U-V||_2^2 <=8 E(U)/kappa.                           (CCM4)
```

The complements in `(CCM3)` may instead be supplied by flexible padding:
adjoin the `pi`-complement type to the `sigma` side and the
`sigma`-complement type to the `pi` side, then extend `V` by the two identity
cross-matches.  Each side adds at most `4E(U)d/kappa` dimensions.
Thus arbitrary cross-packet mixing between already authenticated congruence
endpoint types has a dimension- and level-independent support-changing
repair.  In particular, it cannot produce an `o(1/D)` endpoint-energy
countersequence while moving positive physical multiplicity mass.

## Proof

Let

```text
K=Hom_Q(sigma,pi) <= M_d
```

and let `Z` be the Hilbert--Schmidt orthogonal projection of `U` onto `K`.
The uniform gap on `pi tensor conjugate(sigma)` gives

```text
delta:=||U-Z||_2^2 <= E(U)/kappa.                     (CCM5)
```

Equivalently, `Z` is the finite-group average of the contractions
`pi(g)U sigma(g)^*`, so `||Z||_op<=1`.  Since `Z` is an exact intertwiner,
`H=|Z|` belongs to `sigma(Q)'`.  Put

```text
P=1_[1/2,1](H),
P'=range(ZP),
V=polar(ZP).                                          (CCM6)
```

Functional calculus and polar decomposition show that `P,P'` reduce the
two representations and that `V` is an exact partial intertwiner.

On `P^perp`, `||Zv||<=||v||/2`.  Since `U` is unitary,

```text
||(U-Z)v||>=||v||/2.
```

Summing over an orthonormal basis of `P^perp` proves
`tr_d(1-P)<=4delta`; equal rank gives the same estimate for `P'`.  Finally,
the polar factor is the nearest partial isometry to `ZP` in Frobenius norm,
so

```text
||UP-V||_2
 <=||UP-ZP||_2+||ZP-V||_2
 <=2||U-Z||_2.                                       (CCM7)
```

This proves `(CCM3)`, and adding
`||U(1-P)||_2^2=tr_d(1-P)` proves `(CCM4)`.

## Multiplicity interpretation and the remaining gate

If

```text
pi=directSum_lambda S_lambda tensor C^(m_lambda),
sigma=directSum_lambda S_lambda tensor C^(n_lambda),
```

then every exact partial intertwiner has rank at most

```text
sum_lambda dim(S_lambda) min(m_lambda,n_lambda).       (CCM8)
```

Consequently `(CCM3)` also yields

```text
(1/2d)sum_lambda dim(S_lambda)|m_lambda-n_lambda|
 <=4 E(U)/kappa.                                      (CCM9)
```

If `U` already intertwines the common exact BS core, all core-generator
terms in `(CCM2)` vanish; the endpoint involution term alone pays every
global endpoint-type mismatch.  Hence cross-stratum mixing itself is not
the moving-level obstruction after global congruence atoms are known.

The hypothesis that both sides of `(CCM1)` are authenticated representations
of one common congruence quotient is load-bearing.  The five square-free
rows give only an exact BS core and an approximately extending `X`; they do
not select `sigma`, its conductor, or its nonnegative restriction-fiber
multiplicities.  Applying `(CCM5)` before that selection would be circular.
The unresolved global-basin problem in `(GOS1)` is exactly this atom-selection
step, not polar repair of cross-type mass afterward.
