# An exact `S5` model through Kassel (2.9) with an order-three marked word

The relations through (2.9), together with (2.12), do not algebraically kill
`w_beta^4`. Compose permutations from right to left and assign

```text
x_alpha             = (3 4),
x_beta              = (1 3 2 4),
x_(alpha+beta)      = (1 4 2 3),
x_(2alpha+beta)     = (1 4 2 3),
x_(-alpha)          = (1 3 2 4),
x_(-beta)           = (0 1),
x_(-(alpha+beta))   = (0 1 2)(3 4),
x_(-(2alpha+beta))  = (0 4 2 3).
```

Direct multiplication verifies (2.4)--(2.9) and (2.12) exactly. Moreover

```text
w_beta=(0 3 4)(1 2),       w_beta^4=(0 3 4).
```

Thus the marked fourth power has exact order three. It is not central: it
fails to commute with every displayed root generator. Consequently its
omega eigenspace is not invariant under the tuple, so this is not yet an
omega-sector representation. Any obstruction at (2.9) must therefore use
scalar centrality, not a group identity killing the order-three word.

The tempting exceptional-cover repair also fails. Under
`Sp4(F2) ~= S6`, root transvections correspond to transpositions. The
exceptional triple cover restricts centrally to `3.A6`, but its extension
over `S6` is noncentral: odd permutations invert the `C3` kernel. Hence a
root lift swaps the omega and omega-squared sectors. It cannot preserve one
space on which the kernel is the scalar `omega I`.

References: the ATLAS of Finite Group Representations entry for `3.S6`
(including its degree-18 permutation representation and projective
presentation check), and the classical exceptional Schur multiplier facts
for `A6` and `S6`.

