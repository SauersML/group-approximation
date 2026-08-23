---
rg: 2
id: iwahori-weyl-coboundary-admits-row-tame-target
kind: claim
title: The regular Weyl coboundary has a correcting gauge whose target remains in the two-row Iwahori basin
distinct_from:
  iwahori-cubics-control-aggregate-weighted-bs-orbit-energy: that asks for the final small-gauge or weighted-energy conclusion; this asks only for a possibly large exact coboundary gauge whose corrected endpoint retains small involution and first-cubic rows, after which global pairwise coercivity makes the gauge small automatically.
  bs14-relative-involution-extension-stability: that repairs an approximate extender all the way to an exact endpoint, with flexible padding; this asks only for another approximate endpoint over the same core and only controls two of its rows.
  regular-iwahori-relative-congruence-exactification: that authenticates congruence vertex representations in the regular sector; this is a direct same-core selection statement which does not prescribe a congruence level or exact endpoint type.
---

Use the square-free Iwahori coordinates after exactifying the `BS(1,4)` core:

```text
RTR^(-1)=T^4,
X^2 approximately 1,       (XR)^2 approximately 1,
(XT)^3 approximately 1,    (XT^2R)^3 approximately 1.       (RCT1)
```

Let `Z={T}'`, `psi=Ad(R^(-1))`, and let `e'_reg` be the centered,
fixed-algebra-removed projected Weyl residual in the unitary coboundary
convention of `solenoid-absorption-cascade-converges`.  If the total
normalized-HS presentation defect is `delta`, prove that one can choose a
unitary `c in Z` such that, after the already allowed `O(delta)` fixed/holonomy
residual is discarded,

```text
e'_reg=c psi(c)^(-1),                                  (RCT2)
X_0=c^(-1)X,                                           (RCT3)
||X_0^2-1||_2+||(X_0T)^3-1||_2<=C delta.              (RCT4)
```

No a-priori bound on `||c-1||_2` is requested.  That bound is automatic:
the original `X` satisfies the same two rows with defect at most `2 delta`,
and `X=cX_0` with `[c,T]=0`, so the exact pairwise theorem
`same-core-involution-cubic-gauge-coercivity` gives

```text
||c-1||_2<=C' delta.                                   (RCT5)
```

Thus this claim isolates endpoint **selection**, not Fourier decay, a Fox
singular-value gap, or integration of a differential.  It is strictly weaker
than exact relative repair: `X_0` may retain inversion, second-cubic, and
other endpoint defects, provided the two rows which globally price its
relative gauge remain small.

## Attempts

- **Minimum inverse-Koopman solution.**  Choosing the minimum-norm linear
  inverse of the projected residual does not prove `(RCT4)`: multiplication
  by the resulting unitary gauge mixes Koopman modes, and normalized-HS
  Taylor remainders are not dimension-free.  The all-endpoint Fox identity
  removes the singular-value issue but not this finite endpoint-selection
  issue.
- **Geodesic integration.**  The exact finite-difference identity

  ```text
  c=v alpha(u)^(-1)
  ```

  for the relative involution and cubic increments makes path integration
  unnecessary.  It also shows exactly where it stops: a large correcting
  gauge is possible only if every corrected endpoint leaves the two-row
  basin.  Proving that one target does not leave is `(RCT4)`.
- **Known long-cycle gauges.**  The movable first-mode packet passes
  `(RCT2)--(RCT4)` by taking the original exact endpoint as `X_0`.  The
  two-jump plateau packet is charged by the involution row and likewise
  cannot violate `(RCT4)` around an exact endpoint.
- **Known flexible outliers.**  The compressed even-Weil packet has zero
  Weyl/inversion residual, so `c=1` satisfies this claim even though exact
  same-dimensional repair fails.  Hence `(RCT4)` does not secretly demand
  strict stability and is compatible with necessary one-line padding.
- **Surviving enemy.**  A counterexample must exhibit genuine cross-packet
  endpoint recycling: the Weyl residual is a regular coboundary, the
  original four rows are small, but every gauge realizing that coboundary
  moves the endpoint out of at least one of `X^2` or `(XT)^3` by order one.
  Neither scalar low modes, heterogeneous direct sums of exact endpoints,
  nor the canonical compressed Weil blocks have this property.

