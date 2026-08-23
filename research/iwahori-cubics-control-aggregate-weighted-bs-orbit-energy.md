---
rg: 2
id: iwahori-cubics-control-aggregate-weighted-bs-orbit-energy
kind: claim
title: The Iwahori rows control aggregate weighted BS-orbit energy after movable-gauge optimization
distinct_from:
  iwahori-cubics-suppress-low-bs-orbit-modes: that demanded an extra positive power of every individual band and is refuted by a single movable exact gauge; this asks only for the summed inverse energy which that family saturates harmlessly.
  weyl-defect-koopman-spectral-regularity: that is the global operator statement consumed by the absorption cascade; this is its explicit finite-cycle, gauge-aware inequality over exact BS packets.
  koopman-weighted-energy-is-linearized-gauge-distance: that identifies the weighted sum with the minimum linearized correcting-gauge norm; this asks the cubic relators to bound that norm by the full presentation defect.
  two-jump-cycle-refutes-functional-calculus-gauge-bound: that rules out obtaining a nonlinear correcting-gauge modulus from small coboundary residual alone; this asks the full cubic energy to exclude or pay for the two-jump plateaux.
---

**OPEN CORRECTED FINITE INEQUALITY.**  In the exact-`BS(1,4)` setup of
`iwahori-cubics-suppress-low-bs-orbit-modes`, let `e'` be the centered,
fixed-algebra-removed projected Weyl residual and let `P_t` be its dyadic
Koopman bands.  Prove directly from the full Iwahori relator energy that

```text
sum_(t dyadic, 0<t<=1) t^(-2) ||P_t e'||_2^2
 <= C delta^2.                                         (IAG1)
```

Equivalently, permit a base-commutant coboundary correction `c` with
`||c-1||_2<=C delta`, reoptimize the residual by that correction, and prove
the same bound for the unabsorbed regular component.  The fixed component
is handled separately by its direct `O(delta)` estimate.

The movable-gauge counterpacket in
`movable-weyl-gauge-refutes-iwahori-cubic-low-mode-gain` shows the scale in
`(IAG1)` is sharp: on one band its numerator is `Theta(delta^2 t^2)`, so no
positive extra power of `t` can hold.  But its contribution to the sum is
only `Theta(delta^2)`, exactly the allowed budget.  Thus `(IAG1)` asks the
two cubics to prevent *simultaneous recycling over many low bands*, rather
than to suppress every legitimate correcting gauge separately.

On each finite fourth-power cycle `(IAG1)` is a weighted discrete Fourier
inequality.  Proving it uniformly, including heterogeneous packet mixtures,
is the remaining arithmetic estimate; neither bare BS dynamics nor the
false pointwise Carleson gain supplies it.

By `koopman-weighted-energy-is-linearized-gauge-distance`, the left side is
equivalent within a factor four to the squared minimum norm of the
linearized base-commutant gauge which absorbs `e'`.  Accordingly `(IAG1)`
is more precisely a nonlinear metric-regularity/error-bound theorem for the
full Iwahori relation map modulo exact gauges.  Its differential at exact
congruence points is covered by `iwahori-uniform-infinitesimal-rigidity`;
the live content is uniform nonlinear integration outside an operator-norm
tube.  This rules out treating `(IAG1)` as a consequence of lacunary trace
decay alone.

The exact two-jump packet in
`two-jump-cycle-refutes-functional-calculus-gauge-bound` also rules out a
generic nonlinear upgrade by spectral functional calculus: an exact unitary
coboundary can converge to one in normalized HS while every correcting
gauge stays `sqrt(2)` away from the identity modulo fixed gauges.  Therefore
the cubic rows must control the large phase plateaux themselves.  Removing
the two small jump projections or taking a polar part cannot suffice.

After an exact extending involution over the same BS core has been found,
`same-core-involution-cubic-gauge-coercivity` gives a stronger conclusion
than `(IAG1)`: the involution row plus the first cubic globally bound every
unitary root-commutant gauge with constant one.  Hence the weighted spectral
estimate is needed, if at all, only as a basin-capture device before such an
exact extension is authenticated.  It is not a residual low-mode problem
inside an exact extendable basin.
