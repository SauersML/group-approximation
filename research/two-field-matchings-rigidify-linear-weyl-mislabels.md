---
rg: 2
id: two-field-matchings-rigidify-linear-weyl-mislabels
kind: claim
title: Two field matchings eliminate every linear Weyl relabeling error
distinct_from:
  bounded-degree-entangled-agreement-pauli-metapixel: that asks for soundness against arbitrary operator strategies; this proves the exact algebraic sampler statement on the linear-translation sector.
  bounded-neighbor-pauli-needs-growing-equality-components: that treats unrelated bounded-degree pairwise Pauli variables; here the same-basis BLR decoder has already made both observable families exact additive representations.
---

ESTABLISHED.  Let `V=F_(2^n)` regarded as an `n`-dimensional vector space
over `F_2`, let

```text
<x,y> = Tr_(F_(2^n)/F_2)(xy),
```

and choose `alpha` with `F_2(alpha)=F_(2^n)`.  Suppose a linear map
`L:V->V` obeys the desired Weyl sign on the two matching families

```text
<b,Lb>       = <b,b>,
<alpha b,Lb> = <alpha b,b>                         (TFM1)
```

for every `b in V`.  Then `L=I`.

Equivalently, after exact same-basis linearity has produced an honest Weyl
translation model `X(a),Z(Lb)`, the two cross-test matchings

```text
(a,b)=(b,b),       (a,b)=(alpha b,b)               (TFM2)
```

exclude every nontrivial linear relabeling while using only two incidences
per `b`.  The complete `V x V` twisted-commutation table is unnecessary on
this sector.

The statement has a uniform quantitative gap.  If `L!=I`, then at least one
of

```text
q_0(b)=<b,(L-I)b>,       q_1(b)=<alpha b,(L-I)b>
```

is a nonzero Boolean polynomial of degree at most two.  Every nonzero
degree-at-most-two polynomial on `F_2^n` has relative Hamming weight at least
`1/4`.  Consequently, if the verifier chooses the two matchings with equal
probability, every nonidentity linear relabeling fails with probability at
least `1/8`.  In squared normalized Hilbert--Schmidt energy, a wrong Weyl
sign contributes `4`, so the average two-matching energy is at least `1/2`.
These constants are independent of `n`.

## Proof

Put `M=L-I` and define the binary bilinear form

```text
B(x,y)=<x,My>.
```

The first identity in `(TFM1)` says `B(b,b)=0` for every `b`.  Over
characteristic two, polarization gives

```text
B(x,y)=B(y,x),
```

so `B` is alternating.  The second identity says that

```text
B(alpha b,b)=0
```

for every `b`.  Polarization of this quadratic form gives

```text
B(alpha x,y)=B(alpha y,x)=B(x,alpha y).             (TFM3)
```

Iterating `(TFM3)` and using linearity shows

```text
B(f(alpha)x,y)=B(x,f(alpha)y)
```

for every `f in F_2[t]`.  Since `alpha` generates the field, `B` is balanced
over `F_(2^n)`.  Hence there is a unique `c in F_(2^n)` with

```text
B(x,y)=Tr(cxy).                                     (TFM4)
```

(take the linear functional `y |-> B(1,y)` and use nondegeneracy of the
trace pairing).  Alternation now gives

```text
Tr(cx^2)=0
```

for every `x`.  Squaring is a bijection of the finite field, so
nondegeneracy of the trace pairing forces `c=0`.  Thus `B=0`, whence `M=0`
and `L=I`.

For the quantitative assertion, exact rigidity shows that for `L!=I` one of
`q_0,q_1` is nonzero.  The elementary Reed--Muller distance bound says that a
nonzero multilinear polynomial of degree at most `r` on `F_2^n` has weight
at least `2^(-r)`: restrict to a variable occurring in a top-degree monomial
and induct on the number of variables.  Taking `r=2` gives the claimed
quarter-density, and averaging the two matchings gives `1/8`.

## Scope

This is not yet the entangled sampler theorem.  A general exact
representation of the two additive observable groups may move the
`X`-character fibers by a nonlinear commuting action or by multiplicity
intertwiners rather than one global translation `L`.  The remaining
metapixel theorem must prove that the two matching tests reduce that action
to the linear sector on positive mass, or exhibit an additional bounded
matching which does so.

## Attempts

- One matching `a=b` is insufficient: it only says that the error form is
  alternating, leaving `n(n-1)/2` binary degrees of freedom.
- The second matching cannot be an arbitrary repeated coordinate shear.  Its
  multiplier must generate the full field so that `(TFM3)` balances the form
  over every scalar.
