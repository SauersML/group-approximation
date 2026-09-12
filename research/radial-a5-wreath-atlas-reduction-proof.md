---
rg: 2
id: radial-a5-wreath-atlas-reduction-proof
kind: route
title: Parametrize factor-swap involutions and read radial contexts as V4 cosets
target: radial-a5-socle-extension-is-a-v4-coset-atlas
requires:
  - radial-simplex-excludes-partitioned-involution-targets
---

In `(A5 x A5) semidirect C2`, an element `(g,h)tau` squares to
`(gh,hg)`, so it is an involution exactly when `h=g^(-1)`.  Write it as
`r_g`.  Direct multiplication gives

```text
r_a r_b=(a b^(-1),a^(-1)b).                             (RWP1)
```

Thus `r_a` and `r_b` commute exactly when `a b^(-1)` is an involution or the
identity.  Taking `a=c` shows that a pairwise commuting family has labels
`d c`, where the nonidentity `d` commute in `A5`.  All such `d` lie in the
unique Klein four carrier determined by any nontrivial pair, giving `(RWA5)`.

Multiplying two elements with labels `d_1c,d_2c` gives the first formula in
`(RWA6)`.  Pairing four factors proves that their product is the identity
exactly when the four `d_j` sum to zero in the elementary abelian group `E`.
This is precisely the radial local relation and proves the equivalence with
the coset atlas.

Finally, a global coset gives a commuting image.  Conversely, if all
coordinate images commute, fix one `r_c`; every relative label is an
involution commuting with every other relative label, so all lie in one
Klein four `E` and all labels lie in `Ec`.  This proves the abelianity
criterion.  Carrier overlap and connectedness of the swap-coset commuting
graph follow because each involution of `A5` lies in one of its five Klein
four groups and the full involution conjugacy class generates `A5`.
