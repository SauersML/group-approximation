---
rg: 2
id: congruence-slot-escapes-ultraproduct-lambda-algebra-proof
kind: route
title: Regular trace makes pi(h) orthogonal to every pi(lambda), although co-density puts pi_m(h) in the coordinate algebra
target: congruence-slot-escapes-ultraproduct-lambda-algebra
requires: []
---

**(i)**  For fixed `g != e` in `Gamma` write `g - 1 = p^(-a) N` with `N` a
nonzero integer matrix.  Since `p` is a unit modulo `n_m`, the image of
`g` in `G_m` is trivial iff `n_m` divides every entry of `N`, which fails
once `n_m > max |N_(ij)|`.  Hence `tau_m(pi_m(g)) = [g = e in G_m] = 0`
for all large `m`, so `tau(pi(g)) = delta_(g,e)`: the trace is regular.
The `Lambda`-restriction of `pi_m` is the genuine representation
`lambda_(G_m) o (Lambda -> G_m)`, which factors through `SL_3(Z/n_m)` with
`gcd(n_m, p) = 1`: exact of coprime type.  Since `lambda_(h,m) = h` in
`G_m`, `V'_m = pi_m(lambda_(h,m)) = pi_m(h)`, so `W = V'^* pi(h) = 1`.

**(ii)**  Reduction `Lambda = SL_3(Z) -> SL_3(Z/n_m)` is onto (strong
approximation for `SL_3`, or directly: `SL_n(Z) -> SL_n(Z/N)` is surjective
for every `N`).  Hence `pi_m(Lambda) = pi_m(Gamma) = lambda_(G_m)(G_m)` as
sets, and `pi_m(h) in W^*(pi_m(Lambda))`.

**(iii)**  For every `lambda in Lambda`, `lambda^(-1) h != e` (as
`h notin Lambda`), so by (i) `tau(pi(lambda)^* pi(h)) = tau(pi(lambda^(-1) h)) = 0`.
Thus `pi(h)` is orthogonal in `L^2(M)` to `span pi(Lambda)`, which is a
`*`-algebra (the span of a group image) and is `||.||_2`-dense in
`L^2(pi(Lambda)'')` by Kaplansky density.  The conditional expectation
`E_(pi(Lambda)'')` is the orthogonal projection onto that closure, so
`E_(pi(Lambda)'')(pi(h)) = 0`, while `|| pi(h) ||_2 = 1`; hence
`pi(h) notin pi(Lambda)''`.

The consequence paragraph of the claim is read off: (i)-(ii) show the
counterexample satisfies every hypothesis under which the invalidated route
asserts `(RECF1)`, and (iii) shows `(RECF1)` fails for it.
