---
rg: 2
id: mf-nonhyperlinear-collapse-structure-proof
kind: route
title: Read the hyperlinear residual through elementwise visibility
target: mf-nonhyperlinear-collapse-structure
requires: [hyperlinear-elementwise-visibility, mf-finite-normal-tracially-visible, mf-hyperlinear-of-finite-normal-quotient]
artifacts:
  - GroupApproximation/Sofic/RadicalSeparation.lean
---

## Why sufficient

*Identification of the residual.*  Let `g != 1` in a countable group `G`.
If `g` is tracially visible then step 1--2 of the proof of
`hyperlinear-elementwise-visibility` produces normalized Hilbert--Schmidt
models of `G` of arbitrary accuracy in which `g` has trace near `0`; the
induced homomorphism into the unitary group of a tracial matrix ultraproduct
has hyperlinear image and does not kill `g`, so `g` is not hyperlinear
invisible.  Conversely, if `rho:G->H` is a homomorphism into a hyperlinear
group with `rho(g) != 1`, then `rho(g)` is tracially visible in `H` with
constant `1/2` (necessity half of `hyperlinear-elementwise-visibility`), and
pulling models back along `rho` keeps both the defect and the trace, so `g`
is tracially visible in `G`.  Hence for `g != 1`

```text
g in hyperlinearResidual G  <=>  g is not tracially visible.      (S1)
```

By `hyperlinear-elementwise-visibility`, `G` is hyperlinear iff every
`g != 1` is tracially visible, which by `(S1)` is exactly
`hyperlinearResidual G = 1`.

*Item 1.*  If `G` is not hyperlinear then `R = hyperlinearResidual G != 1`
by the equivalence just proved.  For `g` outside `R` there is a hyperlinear
`H` and `rho:G->H` with `rho(g) != 1`; by definition of the residual as an
intersection of kernels, `R <= ker rho`, so `rho` factors through `G/R` and
detects the image of `g` there.  Thus every nontrivial element of `G/R` is
tracially visible and `G/R` is hyperlinear.

*Item 2.*  Let `N <= R` be a finite normal subgroup of `G` with `N != 1`.
Since `G` is MF, `mf-finite-normal-tracially-visible` makes every `g != 1`
in `N` tracially visible, contradicting `(S1)`.  Hence `N = 1`.  Since `R`
is itself normal in `G`, a finite `R` would be such an `N`, so `R` is
infinite.  Finally, if `G` had a nontrivial finite normal subgroup `N` with
`G/N` hyperlinear then `mf-hyperlinear-of-finite-normal-quotient` would make
`G` hyperlinear.  End proof.
