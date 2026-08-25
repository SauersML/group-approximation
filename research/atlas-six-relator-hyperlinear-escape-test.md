---
rg: 2
id: atlas-six-relator-hyperlinear-escape-test
kind: claim
title: The exact six-relator matrix-ultraproduct escape is exactly a bridge-retaining hyperlinear quotient
distinct_from:
  atlas-six-relator-exact-phase-escape-is-a-finite-quotient-test: that treats exact finite-dimensional zeros and reduces them to finite quotients; this treats the genuinely dimension-moving tracial matrix-ultraproduct zero set and reduces it to hyperlinear quotients.
  atlas-five-row-blowup-branch-is-impossible: that eliminates vanishing additive-energy blow-ups; this classifies the remaining positive-energy exact branch group-theoretically.
  atlas-six-relator-leavitt-tracial-countermodel: that gives an exact model in a possibly non-Connes-embeddable factor; this characterizes exactly when such a model exists in a tracial matrix ultraproduct.
  hyperlinear-quotient-permanence-equivalence: that concerns closure of the class of all hyperlinear groups under arbitrary quotients; this is a fixed relative quotient criterion with two injected A8 charts and a fixed finite bridge menu.
---

**ESTABLISHED.**  Put

```text
Gamma_6=(A8_1*A8_2)/<<s_0,s_11,s_30,s_44,s_55,c_19243>>.
```

Let `t_1,...,t_4` be the four fixed standard transvections generating
`H=diag(GL_3(2),1)<A8`, and put

```text
b_ell=i_2(t_ell)i_1(t_ell)^(-1) in Gamma_6.          (HUQ1)
```

The following are equivalent.

1. There is an exact common-orbit model of the six displayed relators in a
   tracial matrix ultraproduct, with both `A8` restrictions equal to their
   regular character.
2. There is a hyperlinear quotient

   ```text
   q:Gamma_6 -> Lambda
   ```

   which is injective on both marked `A8` factors and for which
   `q(b_ell)!=1` for at least one `ell`.

Every model in item 1 automatically has strictly positive five-row additive
energy.  Indeed the exact `19243` relation prevents all four words `(HUQ1)`
from vanishing, and `regular-atlas-linearized-h-coercivity` makes any
surviving bridge pay positive five-row energy.  Thus item 1 is exactly the
macroscopic alternative left by `atlas-five-row-blowup-branch-is-impossible`.

Equivalently, the qualitative endpoint of
`atlas-five-row-operator-phase-lift` says

```text
every hyperlinear quotient of Gamma_6 kills one marked A8 factor. (HUQ2)
```

The bridge formulation is deliberately retained in item 2: it gives the
fixed group-word witness.  On the regular character face it is actually
automatic once both factors inject, because exact `c_19243` and simultaneous
vanishing of the four bridges are incompatible.  Thus the apparently
operator-valued positive-energy exclusion is exactly a relative hyperlinear-
residual statement for this one finitely presented group.

## Direct nonhyperlinear endpoint

The quotient `Gamma_6 -> Q=L_(F_2)(1,2)^x` injects both marked `A8` factors.
The two chart images in `Q` intersect trivially, so every nonidentity standard
transvection gives a fixed surviving bridge word.  Consequently

```text
atlas-five-row-operator-phase-lift
             => Gamma_6 is nonhyperlinear.             (HUQ3)
```

This endpoint does not need the separate canonical-Leavitt separating
refinement.  If `Gamma_6` were hyperlinear, its identity quotient would be
the quotient in item 2, hence would itself supply the forbidden exact
matrix-ultraproduct escape.
