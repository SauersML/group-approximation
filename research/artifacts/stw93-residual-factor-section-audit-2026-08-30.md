# XCIII: residual factor-section and GNS-layer audit

## Canonical splitting after saturation

The canonical map `F(Z)->D` has trace-kernel `J` when viewed in `D/I`.
After quotienting by `K_Z^sat`, its kernel is still exactly `J`: inclusion
of the canonical trace-zero slice gives one containment, while
`K_Z^sat subset I` gives the other.  Therefore

```text
Q=F(Z)/J -> E=D/K_Z^sat
```

is injective and splits `E->D/I=Q`.  The residual extension is consequently
a semidirect split extension

```text
E=R+s(Q),                   R intersect s(Q)=0.
```

The word semidirect matters: no commutation or direct-product decomposition
is asserted.

## Geometry of an extra ordinary trace

Every trace on `E` agrees on the factor section `s(Q)`, because a II_1 factor
has its unique C*-trace.  In the GNS von Neumann algebra of a hypothetical
extra trace, the weak closure of `R` is a central ideal `zM`.  The factor
section closes to a II_1 subfactor `N`.  Centrality of `z` makes
`x -> tau(zx)` a trace on `N`, so factor uniqueness forces

```text
E_N(z)=tau(z)1.
```

Thus an extra trace is a factor-compatible central residual layer, not a
new trace on the quotient.  Any charged residual positive element has a
finite-capacity spectral cut supported under this layer.

## What spectral gap has and has not supplied

Full-free-factor spectral gap is what pushes the canonical tracial central
quotient into the Jiang--Su factor and yields the slice-surjectivity theorem
used by the splitting.  Once the split extension is reached, spectral gap
has no operator-norm control on the central support `z`: the residual ideal
is zero in the canonical tracial representation by definition.  A positive
solution must exclude a nonzero factor-compatible layer using additional
norm-level information, or prove quasitrace linearity and then exclude its
bounded trace.

The theorem concerns ordinary traces and their GNS representations.  An
arbitrary nonlinear quasitrace need not have this von Neumann GNS picture.
