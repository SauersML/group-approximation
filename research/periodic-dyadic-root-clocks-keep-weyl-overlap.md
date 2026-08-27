---
rg: 2
id: periodic-dyadic-root-clocks-keep-weyl-overlap
kind: claim
title: Periodic dyadic root clocks satisfy every Weyl depth shift while keeping independent lamp overlap
distinct_from:
  finite-affine-sl3-root-shell-keeps-interior-overlap: that includes the nonmonomial SL3(F2) incidence and the Weyl triangle but fails the dyadic root-depth equation; this satisfies all six dyadic root-depth equations exactly and identifies the adjacent-root Steinberg commutator as the next missing input.
  rank-two-weyl-triangle-is-first-apartment-gauge-detector: that kills a common inner-slot gauge; this constructs a finite outer root-module action in which no common inner slot exists although the rank-two triangle and periodic BS(1,2) spectral dynamics are exact.
  parabolic-spectrum-is-doubling-invariant: that records the limiting doubling-invariant spectral constraint in the arithmetic group; this gives a literal finite period-four realization and couples it to a balanced commuting-conjugate lamp.
---

Let `Phi={(i,j):1<=i!=j<=3}` be the six roots of type `A_2` and put

```text
R = direct_sum_(alpha in Phi) F_5 e_alpha                 (PDC1)
```

as an **abelian** finite root module.  Let

```text
Lambda = {(m_1,m_2,m_3) in (Z/4)^3 : m_1+m_2+m_3=0}
       isomorphic to (Z/4)^2.                              (PDC2)
```

Because `2` generates `F_5^x`, `Lambda` acts on `R` by

```text
m.e_(ij)(t) = e_(ij)(2^(m_i-m_j)t).                       (PDC3)
```

The Weyl group `W=S_3` permutes coordinates of both `Lambda` and `R`, and
`(PDC3)` is Weyl-equivariant.  Hence the finite semidirect product

```text
L = R rtimes (Lambda rtimes W)                            (PDC4)
```

is well defined.  Let

```text
C_0 = R rtimes W < L.
```

The left action of `L` on the finite coset set `X=L/C_0` has base point
`x_0=C_0` fixed by the full six-root/Weyl packet `C_0`.

## Exact dyadic and rank-two relations

For

```text
mu=(1,0,-1) in Lambda,
h=(0,mu,1) in L,
```

conjugation gives, for every root,

```text
h e_(ij)(t) h^-1 = e_(ij)(2^(mu_i-mu_j)t).               (PDC5)
```

In particular

```text
h e_12(1) h^-1=e_12(2),
h e_23(1) h^-1=e_23(2),
h e_13(1) h^-1=e_13(4),                                  (PDC6)
```

with the inverse-direction equations as well.  These are the exact finite
periodic versions of the arithmetic dyadic root-depth transport.

Let `mu'=s_12 mu` and `mu''=s_23 mu`.  In the coweight module

```text
mu-(mu'')=mu',
```

so the Weyl conjugates `h',h''` satisfy

```text
h(h'')^-1=h'.                                            (PDC7)
```

Thus all three depth-shift directions and their rank-two compatibility are
present simultaneously.

The root spectrum is genuinely periodic rather than collapsed.  In the
regular representation of the cyclic root group `F_5`, the eigenvalues of
`e_12(1)` are the fifth roots of unity, and squaring permutes the four
nontrivial characters in the cycle

```text
zeta -> zeta^2 -> zeta^4 -> zeta^3 -> zeta.              (PDC8)
```

This is the smallest periodic `BS(1,2)` clock escape: the noninvertible map
on the infinite dyadic tower becomes an invertible four-cycle on an odd
finite spectrum.

## Add the balanced lamp

Form the finite permutational wreath product

```text
B = (direct_sum_(x in X) C_2) rtimes L.                  (PDC9)
```

Let `c_x` denote its lamps.  Since `C_0` fixes `x_0`,

```text
[c_(x_0),C_0]=1.
```

The point `h.x_0` is distinct from `x_0`; all lamps commute.  In the left
regular representation of `B`, with

```text
P=(1-c_(x_0))/2,           Q=hPh^-1,
```

one has exactly

```text
tr(P)=tr(Q)=1/2,       [P,Q]=0,       tr(PQ)=1/4.        (PDC10)
```

Therefore the rank-two triangle plus all six dyadic root-depth equations do
not, by themselves, yield any normalized-HS overlap collapse.  Periodic odd
root clocks absorb the depth shift without error while an independent coset
lamp keeps the forbidden profile.

## The next missing relation is multiplicative

The countermodel intentionally makes the six root groups independent and
abelian.  It fails the first adjacent-root Steinberg multiplication triangle:

```text
[e_12(1),e_23(1)] = 1  != e_13(1).                       (PDC11)
```

In the actual arithmetic group,

```text
[e_12(s),e_23(t)]=e_13(st).                              (PDC12)
```

The weight of the target root is the sum of the two source weights, so
`(PDC12)` is exactly the relation that couples the separate period-four
clocks while remaining compatible with `(PDC5)`.

This proves a sharper boundary for the `G_cc` scalar gate:

```text
Weyl triangle + dyadic depth shifts                         insufficient;
Weyl triangle + dyadic shifts + adjacent-root multiplication  next gate.
                                                                    (PDC13)
```

Any dimension-free four-atom/root-spectrum estimate must use `(PDC12)` to
show that the `12`, `23`, and `13` spectral reservoirs cannot all pay for the
lamp transport independently.  A proof based only on separate doubling
invariance in each root direction is refuted by the finite regular models
above.
