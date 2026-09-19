---
rg: 2
id: dyadic-random-lifts-produce-sofic-vertex-action
kind: route
title: Turn amplified compatible vertex actions into orbit charts
target: dyadic-bruhat-tits-vertex-action-is-sofic
requires:
  - dyadic-amplified-edge-random-lifts-exist
---

Fix finite test sets `F subset A`, `E subset A/C_0` and `epsilon>0`, and
apply the required random-lift claim to a normal-form window containing
`F`, `F^2`, representatives `r_x` for `x in E`, and all products used in
the covariance tests.

Use the exact actions `rho_0,rho_1` on the two vertex generating sets and
evaluate a fixed amalgam normal form to define `phi(g)`.  The only changes
in reducing a product of two such normal forms are vertex-group
multiplications, which are exact, and applications of the two edge
identifications.  A fixed test window uses only a fixed number of edge
identifications.  Telescoping the Hamming defects in item 1 therefore makes
`phi` `(F,O_F(epsilon))`-multiplicative.

Let the finite label set be the set of `rho_0(C_0)`-orbits in `Omega`.  For
a good basepoint `omega`, define

```text
pi_omega(x)
  = Orb_(rho_0(C_0))(phi(r_x)^(-1) omega),   x in E.
```

Item 2 makes this chart injective.  Changing a representative on the right
by an element of `C_0` does not change the displayed orbit.  Normal-form
multiplication gives, away from `O_F(epsilon)|Omega|` points,

```text
pi_(phi(g) omega)(g x) = pi_omega(x)
```

for every tested `g,x`.  These are precisely the finite orbit-chart axioms.
Taking the input error smaller by the fixed telescoping constant proves
soficity of `A action A/C_0`.

For clarity, if `c=r_(gx)^(-1) g r_x in C_0`, the pointwise comparison used
above is

```text
phi(r_(gx))^(-1) phi(g) omega
  = rho_0(c) phi(r_x)^(-1) omega
```

outside the union of the finitely many edge-relation defect sets in that
normal-form reduction.  Applying `rho_0(c)` does not change the
`rho_0(C_0)`-orbit label.  Thus the construction really gives one common
approximate `A`-action, not two unrelated local sheet models.
