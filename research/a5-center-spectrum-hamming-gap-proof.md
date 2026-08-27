---
rg: 2
id: a5-center-spectrum-hamming-gap-proof
kind: route
title: Compute the Plancherel collision probability on a moved A5 coordinate cycle
target: a5-center-spectrum-has-constant-one-site-hamming-gap
requires: []
---

The irreducible dimensions of `A5` are

```text
1, 3, 3, 4, 5.
```

In the left regular representation the central block belonging to `pi` has
rank `dim(pi)^2`.  Tensoring over the factors of `Q=A5^F` gives `(ACS1)`, and
an external amplification multiplies all ranks by the same integer.

Let `alpha,beta in Aut(Q)` induce different site permutations and put
`gamma=alpha^(-1) beta`.  The site permutation of `gamma` has a cycle
`(x_1 ... x_l)` with `l>=2`.  An automorphism of `A5` acts on `Irr(A5)` by a
permutation preserving the Plancherel weights (the only possible nontrivial
outer action exchanges the two three-dimensional irreducibles).  If a random
`omega in Omega_F` is fixed by the center action of `gamma`, its colors along
this cycle are determined by the color at `x_1`, subject possibly to one
additional closing constraint.  Therefore

```text
Pr[omega is fixed along the cycle]
 <= sum_pi p_pi^l
 <= sum_pi p_pi^2
 = 29/100.                                               (ACP1)
```

The event that the two center permutations induced by `alpha` and `beta`
agree is the fixed-point event for `gamma`, hence is contained in the event
in `(ACP1)`.  This proves `(ACS2)`.

Finally, every nontrivial irreducible representation of `A5` is faithful:
its kernel is normal, and simplicity leaves only the identity or all of
`A5`; the latter is precisely the trivial representation.  Moreover, if a
tensor product of invertible matrices is the identity, each tensor factor is
scalar.  A scalar in a faithful irreducible image of centerless `A5` comes
from a central group element and is therefore the identity.  A tensor-product
fiber indexed by `omega` is consequently faithful on `A5^Z` exactly when no
coordinate in `Z` carries the trivial representation.  Product Plancherel
measure gives `(ACS3)`.
