---
rg: 2
id: finite-range-block-mass-ucp-upgrade-proof
kind: route
title: Apply the codomain Smith lemma blockwise and overwrite the negligible bad center
target: finite-range-block-mass-upgrades-diverging-positivity-to-ucp
requires: []
---

For each summand in `(FRB1)`, let

```text
pi_(n,j):B_n -> M_(r_(n,j))
```

be its irreducible coordinate map.  If `r_(n,j)<=k_n`, then
`pi_(n,j) phi_n` is unital and `r_(n,j)`-positive.  The codomain form of
Smith's lemma says that an `r`-positive map from an operator system into
`M_r` is completely positive.  Hence `phi_n` is completely positive on
every summand below the positivity threshold.  Amplifying by the concrete
multiplicity `I_(m_(n,j))` preserves complete positivity.

Fix any state `sigma_n:S->C`.  Define `psi_n` blockwise: retain `phi_n` on
the summands with `r_(n,j)<=k_n`, and on every remaining summand use

```text
x |-> sigma_n(x) I_(r_(n,j)) tensor I_(m_(n,j)).           (FRB4)
```

Every block map is ucp, so their direct sum is ucp and unital.  For a
contraction `x`, both the old and new values are contractions because a
unital positive map has norm one.  Their difference is supported on `z_n`
and has operator norm at most two.  Therefore

```text
||psi_n(x)-phi_n(x)||_(2,d_n)^2
 <= 4 tr_(d_n)(z_n)=4 rho_n,
```

which is `(FRB3)`.

If `rho_n->_omega 0`, quotient equality follows on every element of `S` by
homogeneity.  The application to the Maslov generator system uses the maps
and orders supplied by
`maslov-central-regular-lifts-have-diverging-positive-order`.

