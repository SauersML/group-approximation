---
rg: 2
id: infinite-symmetric-groups-miss-a-unimodular-root
kind: claim
title: Full symmetric groups do not solve nonsingular one-variable equations internally, already at degree one
invalidates:
  - kl-via-internal-closure-of-a-universal-group
distinct_from:
  kervaire-laudenbach-nonsingular-conjecture: that asks for a root in some overgroup of the coefficient group; this is about roots inside one fixed ambient group, and its equation has roots in overgroups because its coefficients generate the finite group S_3.
  overgroup-room-does-not-supply-a-root: that shows that enlarging the ambient without supplying a root only restates the conjecture; this shows that the most natural concrete ambient containing every countable group, Sym(Omega), does not supply roots of its own.
  cantor-odometer-has-no-homeomorphism-square-root: that is the analogous failure for Homeo of the Cantor set, and only at degree two; this is Sym(Omega), where the failure already happens at degree one.
---

Let `Omega` be any set with at least three points, and let `a = (0 1)` and
`b = (0 2)` in `Sym(Omega)`.

1. **Degree one.** The equation `x a x a x^(-1) b = 1` has exponent sum `1`
   and no solution `x in Sym(Omega)`.
2. **Degree two.** A transposition is not the square of any element of
   `Sym(Omega)`, so `x^2 (0 1) = 1` has exponent sum `2` and no solution in
   `Sym(Omega)`.

Both equations have roots in overgroups of their coefficient groups. Those
groups are `S_3` and `C_2`; both are finite, hence hyperlinear, so
`kervaire-laudenbach-holds-for-hyperlinear` applies. Neither equation is a
Kervaire--Laudenbach counterexample.

## What it kills

Every countable group embeds in `Sym(N)`. So if `Sym(N)` solved every
nonsingular equation over itself internally, Kervaire--Laudenbach would hold
for every countable group, with the root found inside `Sym(N)`. Item 1 says
this internal closure fails at the unimodular degree itself, so no argument of
the form "the full symmetric group always contains a root" can work at any
degree. Recorded dead: `kl-via-internal-closure-of-a-universal-group`, for
the ambient `Sym(Omega)`.

## Evidence beyond the proof

An exhaustive census on MSI took unimodular words with at most five
occurrences of `x`, coefficients from `{(0 1), (0 2), (0 1 2), 1}`, and all `x`
in `S_K`. It found no root for 4406 of the 20864 words at `K = 3, 4`, and for
4006 at `K = 5, 6`. The word above is the first one listed. Script:
`/scratch.global/sauer354/hl-kl-homeo-universal/search/internal_s.py`. The
census is a sanity check; the proof in
`infinite-symmetric-groups-miss-a-unimodular-root-proof` covers every
`Omega`.
