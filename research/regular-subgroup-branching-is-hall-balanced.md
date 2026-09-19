---
rg: 2
id: regular-subgroup-branching-is-hall-balanced
kind: claim
title: Regular finite-group restriction graphs are always weighted-Hall balanced
---

Let `H<=G` be finite groups.  Put a source vertex at every irreducible
`G`-representation `sigma`, a target vertex at every irreducible
`H`-representation `theta`, and join `sigma` to `theta` when `theta` occurs in
`Res^G_H sigma`.  Give the vertices their regular-isotypic weights

```text
w_G(sigma)=d_sigma^2/|G|,
w_H(theta)=d_theta^2/|H|.
```

Then for every set `S` of source irreducibles,

```text
sum_(sigma in S) w_G(sigma)
 <= sum_(theta in N(S)) w_H(theta).                   (RBH1)
```

Thus the type-incidence graph of restriction of a regular finite-group chart
can never itself supply a weighted Hall deficit.  Any atlas Hall obstruction
must use actual multiplicity-arrow equations, coefficient zeros, or another
relation-sensitive refinement of representation type.

This generalizes the already-audited `S_4 -> S_3` balance: the failure of
bare type counting is not special to that subgroup pair.

This no-go does not apply to coupled multiplication channels.  The exact
local distinction is recorded by
`s3-hard-cell-three-channel-data-is-nondegenerate`: type incidence stays
balanced while the recoupling, full restriction fingerprint, and moment
overlap matrices are all invertible.  Whether the atlas relators expose those
coordinates is the separate open claim `atlas-hard-packet-s3-channel-decoder`.
