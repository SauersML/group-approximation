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
