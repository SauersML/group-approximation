---
rg: 2
id: fixed-core-passive-fiber-has-positive-basin
kind: claim
title: Every fixed passive BS core has a positive finite-fiber completion basin
distinct_from:
  one-core-endpoint-union-is-one-finite-restriction-fiber: that identifies the complete exact endpoint set over one core; this gives the quantitative compactness modulus which exactifies a passive reflection once its residual enters that coordinate's basin.
  authenticated-core-union-basin-is-relative-liftability: that asks for a uniform moving-core retraction; this proves only the strongest unconditional coordinatewise theorem and exposes the missing uniform radius.
  iwahori-uniform-infinitesimal-rigidity: that gives a uniform derivative gap after an exact endpoint orbit has already been selected; this gives a possibly nonuniform global compactness basin around the union of all endpoint orbits over one fixed core.
---

**ESTABLISHED.**  Fix one finite-dimensional exact `BS(1,4)` core

```text
beta=(R,S):B -> U(d).
```

Let `K_beta` be the compact set of reflections satisfying exact inversion,

```text
K_beta={X:X=X*=X^(-1), XRX=R^(-1)},                   (PFB1)
```

and let

```text
Z_beta={X in K_beta:(XS^2)^3=(XRS)^3=1}               (PFB2)
```

be its exact endpoint fiber.  Put

```text
L_beta(X)=||(XS^2)^3-1||_2^2+||(XRS)^3-1||_2^2.       (PFB3)
```

For every `eta>0`, if `Z_beta` is nonempty, then

```text
delta_beta(eta)
 =min{sqrt(L_beta(X)):X in K_beta,
                         dist_2(X,Z_beta)>=eta}>0.    (PFB4)
```

Consequently

```text
sqrt(L_beta(X))<delta_beta(eta)
       => dist_2(X,Z_beta)<eta.                        (PFB5)
```

Every member of `Z_beta` factors through the one finite quotient
`A/<<s^N>>`, where `N=ord(S)`, and its orbit type lies in the finite
restriction fiber determined by `beta`.  Thus `(PFB5)` is a genuine
simultaneous two-face completion theorem, not merely separate rounding of
the two order-three products.

It gives the strongest unconditional triangular repair statement.  After
an authenticated `o(d_n)` active cell has been restored exactly, block-cut
and polarize the passive compression so that it lies in `K_(beta_n)`.  If
its two-cubic residual falls below
`delta_(beta_n)(eta_n)` for some `eta_n->0`, choose
`X_n^0 in Z_(beta_n)` from `(PFB5)`.  Direct-summing the exact active cell
with `(X_n^0,beta_n)` gives an exact endpoint; the passive involution moves
by at most `eta_n`, and the active restoration costs only its energy-paid
`o(d_n)` rank.

There is no dimension-uniform lower bound on `(PFB4)` proved here.  The
assertion that every operator-small passive residual automatically lies
below a suitable moving `delta_(beta_n)(eta_n)` is exactly the relative
coordinate-lift/basin theorem.  Sublinear active surgery leaves that lifting
class unchanged.  Hence local active restoration and fixed-core compactness
close the triangular argument coordinatewise, but do not solve the moving
regular-face endpoint.

DERIVATION
fixed-core-passive-basin-proof
