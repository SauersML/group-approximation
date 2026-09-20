---
rg: 2
id: kt-double-reduced-not-mf-from-nonhyperlinearity
kind: route
title: "Unique reduced trace turns a hypothetical MF embedding into a forbidden hyperlinear model"
target: kt-double-reduced-cstar-is-not-mf
requires:
  - kt-q2-double-is-not-hyperlinear
  - kt-q2-double-reduced-algebra-has-unique-trace
---

## Attribution

The proposed analytic input behind the negative group prerequisite is
Jihao Liu, [*Nonhyperlinear groups exist*](https://jihaoliu.org/ai-results/nonhyperlinear-groups-exist-2026-09-20.pdf)
(2026-09-20), Theorem 1.2 / 6.7 and Theorem 1.3 / 7.4. The conditional
normalization/double construction is due to Andreas Thom,
[Theorems 1.2-1.3](https://andreasthom.github.io/pdf/nonhyperlinear.pdf),
and the pair and lamp construction to Gabor Kun and Andreas Thom,
[Theorems A and E](https://arxiv.org/abs/2608.06222). This route is the
unique-trace consequence for the q=2 family, not a verbatim claim of Liu's
fixed-parameter Theorem 8.3.

Fix any integers `r,d>=3` and use the corresponding `q=2` double `D` of
the target. Suppose its reduced
C-star algebra has an MF embedding into a matrix norm corona. Take the
embedding unital. This entails no loss: its unit is a projection in the
corona, which lifts to coordinate projections by spectral cutting; restrict
to an infinite subsequence where their ranks are positive and then to
those matrix corners.

For a nonprincipal ultrafilter, the norm-null ideal is contained in the
normalized-2-norm-null ideal. Thus composition with the quotient to the
tracial matrix ultraproduct gives a unital star-homomorphism `theta`.
The functional `tau o theta` is a tracial state on `C*_r(D)`. By the unique
trace prerequisite, specialized to this double, it is the canonical
regular trace `tau_D`.

The canonical trace is faithful. If `theta(x)=0`, then
`tau_D(x*x)=tau(theta(x*x))=0`, so `x=0`. In particular the canonical group
unitaries give an injective homomorphism `D->U(M)` in this tracial matrix
ultraproduct; equivalently, for `g!=h`, their squared 2-distance is exactly
`tau_D((lambda_g-lambda_h)*(lambda_g-lambda_h))=2`.
This makes `D` hyperlinear, contrary to the first prerequisite.
Hence no such reduced MF embedding exists. Since `r,d` were arbitrary,
this proves the claim for every parameter choice in its stated scope.
