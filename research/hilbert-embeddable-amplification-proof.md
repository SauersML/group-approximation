---
rg: 2
id: hilbert-embeddable-amplification-proof
kind: route
title: Subordinate by a Bernstein function and tensor the realizing representation
target: hilbert-embeddable-amplification
requires: [glebsky-manufactured-invariant-length]
---

## Direct proof

**Subordination.**  If `psi` is a conditionally negative definite kernel
vanishing on the diagonal and `f` is a Bernstein function with `f(0)=0`, then
`f o psi` is conditionally negative definite.  Write
`f(t)=at+integral (1-exp(-lambda t)) dmu(lambda)`; each `1-exp(-lambda psi)`
is conditionally negative definite because `exp(-lambda psi)` is positive
definite by Schoenberg, and the conditionally negative definite kernels form
a convex cone closed under pointwise limits.

`f_r(t)=1-exp(-rt)` is Bernstein with Levy measure `delta_r` and `f_r(0)=0`;
`min{t,1}` is not, its derivative `1_([0,1))` failing complete monotonicity.
That single difference is the whole content of item 3.

**1.**  `ell_r=f_r o ell` is therefore conditionally negative definite,
conjugation invariant and symmetric because `ell` is, vanishes exactly where
`ell` does, and satisfies `0<=ell_r<=1`.  The elementary bounds
`1-exp(-x)<=x` and monotonicity give `ell_r<=r ell` and
`ell_r>=1-exp(-rc)` on `{ell>=c}`.  With `delta` the defect and `c` the
separation of a witness carrying `ell`, the witness carrying `ell_r` has
defect at most `r delta` and separation at least `1-exp(-rc)`; taking
`r=ceil(delta^(-1/2))` gives `sqrt(delta)+delta` and
`1-exp(-c delta^(-1/2))` respectively.  Both are what item 1 asserts.

**2.**  Realize `exp(-ell)` as `tr rho` for a unitary representation `rho`, as
in `hilbert-embeddable-length-hyperlinearity` item 2.  Then
`tr(rho^(tensor r))=(tr rho)^r=exp(-r ell)`, so `ell_r=1-tr(rho^(tensor r))`.
For the permutation case, `1-d_H(sigma,1)` is the fixed-point fraction, which
is `tr P_sigma`, and the product action on `[m]^r` has fixed-point fraction
the `r`-th power — the same identity.  Since `tr rho=exp(-ell)` is real and
strictly positive, its powers tend to `0` monotonically and no phase
cancellation can hold them away from `0`; this is why the scalar obstruction
to tensor amplification in `U(n)` does not arise here.

**3.**  On the error set `X` every element has word length `1`, so
`d(1,x)/n=1/n` and `1-exp(-1/n)` lies between `1/n-1/(2n^2)` and `1/n`.  On an
`n`-separated `Y` every element has word length exceeding `n`, so
`d(1,y)/n>1` and `1-exp(-d(1,y)/n)>1-exp(-1)>0.632`.  Both profiles match
`min{d/n,1}` up to the absolute constants
`(1-exp(-1)) min{t,1} <= 1-exp(-t) <= min{t,1}`, and the replacement is
conditionally negative definite whenever `d` is, by subordination.

**4.**  Combining: if `d` is conditionally negative definite then so is
`1-exp(-d/n)`, which by 3 has the profile Glebsky's construction needs, and
by 1 its separation may be amplified at will.  Hence the only obstruction to
a Hilbert embeddable witness of Glebsky type is conditional negative
definiteness of the uncapped conjugation-invariant word metric.

## Scope

**Composition hazard (`cairn-verify`, 2026-08-14).**  Item 1 amplifies the
*length*; the criterion's item 2 then exponentiates whatever length it is
handed.  Composing them in that order **loses**: feeding `ell_r` into
`hilbert-embeddable-length-hyperlinearity` item 2 realizes `exp(-ell_r)` and
gives normalized-HS separation `2(1-exp(-ell_r))`, which is capped at
`2(1-e^(-1)) = 1.264...` because `ell_r <= 1`, and so never reaches the
`2-epsilon` that `Sofic/Hyperlinear.HyperlinearModel` requires.  The correct
composition is through item 2 of *this* node: use `rho^(tensor r)` directly,
whose normalized-HS square is `2(1-exp(-r ell)) = 2 ell_r -> 2`.  So the two
nodes compose through the **representation**, never through the length.  Any
lane quoting "the separation constant carries no content" must take the
representation-level route.

Item 4 is one directional: a conditionally negative definite word metric
suffices.  Nothing here shows that a Hilbert embeddable witness forces the
word metric to be conditionally negative definite, so a group whose word
metrics all fail the test is not thereby shown to lack a witness of some
other shape.  In particular this does not decide
`hilbert-embeddable-witness-for-kun-thom-wreath`; it removes two of the three
things that question was thought to require and leaves the third.
