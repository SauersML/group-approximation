---
rg: 2
id: degree-one-laplacian-gap-forces-kesten-gap-in-every-model-proof
kind: route
title: Split the degree-one Laplacian into orthogonal halves and read the lower half as the degree-zero Laplacian through sp(TT*) u 0 = sp(T*T) u 0
target: degree-one-laplacian-gap-forces-kesten-gap-in-every-model
requires:
  - model-spectral-gap-quantifier-ladder
---

Notation is that of the target.  Items 1, 2 and 4 use no prerequisite.
Item 3 cites the rung structure of `model-spectral-gap-quantifier-ladder`
only to name the classes.

## Step 0: the complex identity

The fundamental formula of Fox calculus holds in `Z[F(S_0)]`: for every word
`w`, `w - 1 = sum_(s in S_0) (d w/d s)(s - 1)`.  For `r in R`, map it to
`Z[L]`, where `r = 1`, and get `sum_s bar(d r/d s)(s - 1) = 0`.  Row by row
this is the matrix identity

```text
d_1 d_0 = 0   in M_(R x 1)(Z[L]).
```

If `R` is infinite, replace it by any subset; only `d_1 d_0 = 0` is used,
and `d_1^* d_1` is then a finite sum over a finite subset or is absent.
For the target statement take `R` finite.

## Step 1: two spectral facts in a unital C-star algebra `B`

**(F1)** Let `T in M_(m x k)(A)`.  Embed `T` as the off-diagonal corner `a`
of `B = M_(m+k)(A)`.  Then `TT^* = aa^*` is supported in the `m`-corner and
`T^*T = a^*a` in the `k`-corner.  In any unital algebra
`sp(xy) u {0} = sp(yx) u {0}`.  The spectrum of an element of a corner
`pBp` differs from its spectrum in `B` at most by `0`.  Hence
`sp_(M_m(A))(TT^*) u {0} = sp_(M_k(A))(T^*T) u {0}`.

**(F2)** Let `X, Y >= 0` in `B` with `XY = 0`.  Then `YX = (XY)^* = 0`, so
`X` and `Y` commute and generate a commutative C-star algebra `C`.  Take its
unitization `C~`.  Every character `chi` of `C~` has
`chi(X) chi(Y) = chi(XY) = 0`.  Spectra in `C~` agree with spectra in `B`.
If `lambda != 0` lies in `sp(X)`, some character has `chi(X) = lambda`.
Then `chi(Y) = 0`, so `chi(X + Y) = lambda` and `lambda` lies in
`sp(X + Y)`.  Hence `sp(X) \ {0}` is contained in `sp(X + Y)`.

## Step 2: item 1

Apply `rho` entrywise.  It is a unital `*`-homomorphism, so
`rho(d_1) rho(d_0) = 0`.  Put `T = rho(d_0)`, `X = TT^*` and
`Y = rho(d_1)^* rho(d_1)`, all in `M_(S_0)(A)`.  Then

```text
XY = T (rho(d_1) T)^* rho(d_1) = 0,
```

and `rho(Delta_1) = X + Y`.  By (F2), `sp(X) \ {0}` lies in
`sp(rho(Delta_1))`, which misses `(0,eps)`.  By (F1), `sp(rho(Delta_0))`
and `sp(X)` agree away from `0`.  Hence `sp(rho(Delta_0))` misses `(0,eps)`.

For `(MSG)`, let `S` be the multiset `{e} u S_0 u S_0^(-1)` of size
`1 + 2|S_0|`.  Then `h_S = 1 - Delta_0/(1 + 2|S_0|)`.  So `sp(rho(h_S))`
misses `(1 - eps/(1 + 2|S_0|), 1)`, and `1` is not an accumulation point.
If one insists on the set rather than the multiset, represent `A`
faithfully on a Hilbert space.  Having `0` isolated in the spectrum of the
Laplacian is the same as having no almost invariant vectors in the
orthogonal complement of the invariant vectors, and that condition does not
depend on the finite generating set.  Only the constant changes.

## Step 3: item 2

Suppose `sp(Delta_1)` in `M_(S_0)(C*_max L)` misses `(0,eps)`.  Let `pi` be
any unitary representation of `L` on a Hilbert space `H`.  It extends to a
unital `*`-homomorphism of `C*_max L`, which can only shrink spectra, so
`sp(pi(Delta_1))` misses `(0,eps)`.  By Step 2, `sp(pi(Delta_0))` misses
`(0,eps)`.  Now `ker pi(Delta_0)` is the space `H^L` of invariant vectors,
since `<pi(Delta_0) xi, xi> = sum_(s in S_0) ||pi(s) xi - xi||^2`.  Let `P`
be the projection onto `H^L`.  By the spectral theorem,

```text
sum_(s in S_0) ||pi(s) xi - xi||^2 >= eps ||xi - P xi||^2   for all xi.
```

If a unit vector `xi` has `||pi(s) xi - xi|| < kappa = sqrt(eps/|S_0|)` for
every `s in S_0`, then `||xi - P xi||^2 < |S_0| kappa^2 / eps = 1`.  So
`P xi != 0` and `H^L != 0`.  Thus `(S_0, sqrt(eps/|S_0|))` is a Kazhdan
pair.  If `p_1 = chi_{0}(Delta_1)` lies in `M_(S_0)(C*_max L)`, then by
continuous functional calculus some `(0,eps)` misses the spectrum.  So
item 2 follows.

## Step 4: item 3

Step 2 is uniform in `A` and `rho`.  So for any class of pairs `(A, rho)`,
"`Delta_1` gapped by `eps` along every member" implies "`Delta_0` gapped by
`eps` along every member".  By Step 2's affine identity, the latter gives
`(MSG)` along every member.  The classes named in the target are the rungs
of `model-spectral-gap-quantifier-ladder`: all Hilbert spaces (rung 0),
corona homomorphisms (rung 1), and the undecided tracial and stably finite
rungs.  So on each rung the degree-one prerequisite implies the degree-zero
one, and the degree-one prerequisite is never strictly weaker.

The converse is not claimed.  A degree-one gap also needs `range d_1` to be
closed along the model (reduced `H^2`), so it can be strictly stronger.
Strength in that direction is useless for removing `(T)`.

## Step 5: item 4

Take `R` empty, so `d_1` is absent and `Delta_1 = d_0 d_0^*`.  In `C*_r F_m`
with `m >= 2`, Kesten gives `||lambda(k)|| = sqrt(2m-1)/m < 1` for
`k = (1/2m) sum_s (s + s^(-1))`.  So `lambda(Delta_0) = 2m(1 - lambda(k))`
is invertible, and by (F1) `lambda(Delta_1)` has spectrum in
`{0} u [2m(1 - sqrt(2m-1)/m), infinity)`.  This is consistent with the
Li--Nowak--Pooya model test recorded on
`reduced-higher-kazhdan-projection-kk-witness`.  In `C*_max F_m`, item 2
would make `F_m` Kazhdan, which it is not, since it surjects onto `Z`.  So
no maximal `p_1` exists.

## Step 6: the kill and its limit

A Property-(T)-free corner argument needs a projection in the model that
sees `L`-invariant vectors of the degree-zero cochains.  In a cochain Euler
relation the degree-zero cochains enter only through `p_0` (the Kazhdan
projection itself) or through the lower half of `Delta_1`.  Step 2 shows
that a gap on the lower half is a degree-zero gap in the same model.  The
truncated complex starting at `C^1` carries the projection onto `ker d_1`
when `d_1^* d_1` is gapped, and that needs no `(T)`.  But
`ker d_1 = ker Delta_1 (+) closure(range d_0)` in every Hilbert-space model.
Having the projection onto `closure(range d_0)` in the model means
`d_0 d_0^*` is gapped at `0`.  By (F1) that is the same as `Delta_0` being
gapped, so splitting `ker d_1` again is exactly the degree-zero hypothesis.  In degree `n >= 2`
the lower half of `Delta_n` is `d_(n-1) d_(n-1)^*`.  By (F1) it controls
only the upper half `d_(n-1)^* d_(n-1)` of `Delta_(n-1)`, and there is no
further step down.  That is exactly where this obstruction stops, and
degree `>= 2` is left open.
