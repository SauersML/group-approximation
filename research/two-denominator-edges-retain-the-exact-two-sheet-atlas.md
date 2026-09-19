---
rg: 2
id: two-denominator-edges-retain-the-exact-two-sheet-atlas
kind: claim
title: Two commuting denominator edges still retain an exact two-sheet atlas
artifacts:
  - research/two-denominator-edges-and-coweight-triangle-proof.md
distinct_from:
  single-hecke-edge-has-exact-two-sheet-atlases: that gives the one-edge HNN countermodel; this extends the same countermodel across two commuting Weyl-conjugate denominator directions and identifies the first relation which it cannot satisfy.
  coweight-triangle-charges-every-common-sheet-flip: that is the sharp obstruction after the third direction and its triangle relation are imposed; this is the positive two-edge half of the calculation.
  six-chamber-a2-holonomy-closes-fixed-clock-sector: that uses the six root packets and the Coxeter hexagon to close a common finite root clock; this concerns only the coarse coset sheet and needs no root-clock exactification.
  two-torus-closures-detect-denominator-multiplicity: that supplies the unbalanced third-side relation and charges a product-form multiplicity twist; this proves the two balanced sides before that relation is imposed still admit a literal finite sheet flip.
---

Fix a prime `p` and put

```text
Lambda=SL_3(Z),
d_12=diag(p,p^(-1),1),
d_23=diag(1,p,p^(-1)).                                  (DTA1)
```

For `r in {12,23}`, let

```text
I_r=Lambda cap d_r^(-1)Lambda d_r,
phi_r(c)=d_r c d_r^(-1)  (c in I_r),                    (DTA2)
```

and form the partial rank-two actor

```text
E_12,23=<Lambda,s,t |
  s c s^(-1)=phi_12(c)  (c in I_12),
  t c t^(-1)=phi_23(c)  (c in I_23),
  [s,t]=1>.                                               (DTA3)
```

For every `m>=2` coprime to `p`, this group has an exact finite action on

```text
Omega_m=SL_3(Z/mZ) x Z/2                                (DTA4)
```

and a label `ell(x,j)=j` such that `Lambda` preserves `ell`, while both
`s` and `t` reverse it at every point.

Thus even two commuting parahoric transporters, their complete integral
overlap-conjugacy tables, and the relation between the two transporters do
not obstruct the common sheet flip.  The first obstruction is the third
Weyl-conjugate direction and the coweight triangle recorded in
`coweight-triangle-charges-every-common-sheet-flip`.

This is only a theorem about the stated partial presentation.  It does not
give an action of `SL_3(Z[1/p])`, and it does not make the arithmetic coset
action sofic.

DERIVATION
two-denominator-edges-and-coweight-triangle-proof
