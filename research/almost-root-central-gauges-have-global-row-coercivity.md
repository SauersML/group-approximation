---
rg: 2
id: almost-root-central-gauges-have-global-row-coercivity
kind: claim
title: Almost root-central extender gauges have dimension-free global row coercivity
distinct_from:
  same-core-involution-cubic-gauge-coercivity: that assumes the relative gauge commutes exactly with the retained root; this proves the robust estimate with the root commutator as one additional error term.
  iwahori-newton-closes-near-sector: that enters an operator-norm coordinate basin and integrates a differential inverse; this is a global normalized-HS finite-word identity with no smallness or operator-norm hypothesis.
  bs14-relative-involution-extension-stability: that must select an exact endpoint and control the root commutator for every packet mixture; this closes the repair after those data have been supplied.
---

Let `x_0,x_1,t` be unitaries on one finite-dimensional Hilbert space and
write

```text
c=x_1 x_0^(-1),               A=x_0t.                 (ARC1)
```

Then, for normalized Hilbert--Schmidt norm,

```text
||c-1||_2
 <= ||x_1^2-x_0^2||_2
    +||(x_1t)^3-(x_0t)^3||_2
    +||[c,t]||_2.                                    (ARC2)
```

In particular, if `(x_0,r,t)` is one exact square-free Iwahori endpoint
over an exact `BS(1,4)` core `(r,t)`, then every unitary `x_1` satisfies

```text
||x_1-x_0||_2
 <= ||x_1^2-1||_2+||(x_1t)^3-1||_2+||[x_1x_0^(-1),t]||_2. (ARC3)
```

Thus the root-central spectral regime of
`bs14-relative-involution-extension-stability` has a dimension-free strict
repair, with linear modulus and no padding.  The inversion and second-cubic
rows are not needed after the exact endpoint on the same core has been
selected.

On a scalar fourth-power packet, diagonalize

```text
t=diag(mu_1,...,mu_d),              c=(c_ij).          (ARC4)
```

The remaining hypothesis is exactly the root-frequency energy

```text
||[c,t]||_2^2
  =(1/d) sum_(i,j) |mu_i-mu_j|^2 |c_ij|^2.            (ARC5)
```

Consequently `(ARC3)` applies uniformly to arbitrary packet lengths and
return phases whenever the relative gauge has vanishing mass away from the
near-diagonal root-frequency bands.  No minimum root spacing is required:
small spectral gaps are weighted by their actual chordal distance in
`(ARC5)`.

This does not select `x_0`.  Exact same-core endpoints can lie in different
root-gauge components, and `p3-exact-iwahori-endpoints-refute-arbitrary-baseline-alignment`
shows that an arbitrary baseline can have a large commutator even at zero
presentation defect.  The unresolved global theorem must therefore choose
a compatible endpoint for which `(ARC5)` is small, or pay the complementary
root-frequency mass by flexible boundary surgery.  Once such an endpoint
is chosen, approximate promotion of its gauge into `{t}'` is no longer a
separate rounding problem: `(ARC2)` consumes the raw commutator directly.

