---
rg: 2
id: iwahori-cubics-control-aggregate-weighted-bs-orbit-energy
kind: claim
title: The Iwahori rows control aggregate weighted BS-orbit energy after movable-gauge optimization
distinct_from:
  iwahori-cubics-suppress-low-bs-orbit-modes: that demanded an extra positive power of every individual band and is refuted by a single movable exact gauge; this asks only for the summed inverse energy which that family saturates harmlessly.
  weyl-defect-koopman-spectral-regularity: that is the global operator statement consumed by the absorption cascade; this is its explicit finite-cycle, gauge-aware inequality over exact BS packets.
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

## Same-core finite-cycle part is settled

`same-core-gauge-rows-control-linearized-koopman-inverse-energy` proves the
complete linearized weighted estimate with universal constant `2` at
**every** unitary over an exact `(R,T)` core, including nonextendable
outliers.  In fact the involution row and first cubic alone give

```text
sum_t t^(-2)||P_t D A||_2^2
 <=2(||L_(x^2)A||_2^2+||L_((xt)^3)A||_2^2).
```

The proof is an exact Fox-row identity and covers arbitrary cycle
lengths, return multiplicities, heterogeneous direct sums, and cross-block
commutant gauges; it does not assume that either row vanishes at the base
point.  The accompanying finite probe checks exact projective packets
through fourth-power orbit length `53`, repeated/heterogeneous sums, and
compressed even-Weil outliers, with no loss.

Therefore the phrase "remaining arithmetic estimate" above must be read
nonlinearly: the unresolved step is to integrate this everywhere-coercive
Fox differential in normalized HS while permitting flexible endpoint
selection and boundary padding.  It is not an unresolved generalized
singular-value estimate on fourth-power cycles.  The compressed even-Weil
outliers have zero Weyl/inversion residual and hence do not challenge the
weighted estimate; they locate the missing content in nonlinear boundary
padding and endpoint selection.

There is in fact no need to integrate the differential.  The upgraded
pairwise identity in `same-core-involution-cubic-gauge-coercivity` compares
two finite endpoint row values directly and proves

```text
||c-1||_2
 <= defect_(x^2)(X)+defect_(x^2)(c^(-1)X)
   +defect_((xt)^3)(X)+defect_((xt)^3)(c^(-1)X).       (IAG2)
```

Accordingly the remaining nonlinear input is decomposed as the narrower
claim `iwahori-weyl-coboundary-admits-row-tame-target`: select a coboundary
gauge whose corrected endpoint has the last two defects in `(IAG2)` of
order `delta`.  Route `row-tame-weyl-correction-proves-aggregate-energy`
then gives the desired small gauge with no Fourier, Taylor, or geodesic
loss.  This selection claim allows an approximate target and is strictly
weaker than full relative Iwahori repair.
