---
rg: 2
id: finitely-generated-map-lef-regular-chart-countermodel-proof
kind: route
title: Put LEF windows in finite regular representations and use simplicity plus Malcev against global correction
target: finitely-generated-map-lef-has-perfect-regular-chart-microstates
requires:
  - ffgs-local-hs-examples-resist-split-finite-presentation-wrappers
---

Choose an increasing exhaustion `F_n` of `H` by finite sets, closed under all
products and inverses needed in the `n`th multiplication table.  LEF gives a
finite group `Q_n` and an injective partial homomorphism

```text
theta_n:F_n->Q_n.                                                        (FRP1)
```

Extend `theta_n` arbitrarily off `F_n` and compose with the left regular
representation of `Q_n`.  Every fixed multiplication equation and every
fixed nonidentity test lies in `F_n` eventually.  It is then exact, and the
normalized trace of its image is respectively `1` at the identity and `0`
away from it.  This proves the microstate assertion.

If `K<=H` is finite, enlarge the tested window to contain all of `K` and its
multiplication table.  Then `theta_n|K` is an injective homomorphism.  As a
left `K`-set, `Q_n` is the disjoint union of its left `theta_n(K)`-cosets;
hence

```text
lambda_(Q_n)|K = [Q_n:theta_n(K)] lambda_K.                              (FRP2)
```

The same single partial homomorphism handles any prescribed finite family
of subgroups, inclusions and overlap equations.  Their regular charts are
therefore restrictions of one common `Q_n`-action, proving the exact
finite-window synchronization statement.

It remains to exclude a genuine correction.  Since `H` is infinite simple,
the kernel of any nontrivial finite-dimensional unitary representation is
trivial.  Its image is finitely generated and linear, hence residually finite
by Malcev.  Pulling back a finite quotient which separates a nonidentity
image element would give a nontrivial finite quotient of `H`, impossible for
an infinite simple group.  Thus every finite-dimensional representation of
`H` is trivial.

For fixed `1!=g in H`, injectivity in `(FRP1)` gives
`theta_n(g)!=1` eventually.  The regular matrix
`lambda_(Q_n)(theta_n(g))` has normalized trace zero, so

```text
||lambda_(Q_n)(theta_n(g))-I||_2^2
 =2-2 Re tr(lambda_(Q_n)(theta_n(g)))=2.                                (FRP3)
```

If `V` is any isometry into a space carrying a trivial representation, then
`||V phi_n(g)-V||_F^2/dim(phi_n)=2` as well.  Adding or deleting `o(dim)`
coordinates cannot remove a fixed lower bound.  This proves `(FRL3)` and
the claim.

