---
rg: 2
id: spherical-fixed-order-cap-codegrees-proof
kind: route
title: Sum the cap inequalities and compare with the norm of the sum of separated centres
target: spherical-fixed-order-cap-codegrees
requires:
  - trace-separation-sphere-distance-concentration
---

Fix any `rho<1`; for concreteness take `rho=1/4`.  By
`trace-separation-sphere-distance-concentration` and a finite union bound, for
all but `o(1)` input points `x` every distinct pair among the selected centres
satisfies

```text
Re <a_i,a_j> <= rho.
```

Suppose `y` lies in all `m` radius-one caps.  Realifying `C^d`, each cap
condition is

```text
Re <y,a_j> >= 1/2.
```

Let `A=a_1+...+a_m`.  Then

```text
Re <y,A> >= m/2,
||A||^2
 = m + 2 sum_(i<j) Re<a_i,a_j>
 <= m + m(m-1)rho.
```

Therefore the whole intersection lies in the single cap around
`A/||A||` with threshold

```text
c_(m,rho)
 = (m/2)/sqrt(m+m(m-1)rho)
 = sqrt(m)/(2 sqrt(1+(m-1)rho)).
```

Because `m>=2` and `rho<1`, one has `c_(m,rho)>1/2`.  On the real sphere
`S^(2d-1)`, the first-coordinate density is proportional to
`(1-t^2)^((2d-3)/2)`.  Exactly as in
`spherical-candidate-pairwise-codegrees-proof`, a cap with any fixed threshold
strictly larger than `1/2` has measure exponentially small relative to the
radius-one cap.  Hence the `m`-fold intersection has measure `o(p_d)`.

There are only finitely many fixed word-tuples in the tested window, so the
exceptional input probability remains `o(1)`.  Conditional on a good input,
independent output samples turn the true cap probabilities into empirical
degrees and `m`-fold codegrees by binomial concentration.  Taking `N(d)` large
enough for `N p_d` to dominate the finite logarithmic union cost makes all
these estimates simultaneous.  No higher-order trace information enters: the
geometry uses only the pairwise inner-product bounds.
