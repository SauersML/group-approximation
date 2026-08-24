---
rg: 2
id: fixed-mf-radical-membership-is-sigma2-complete
kind: claim
title: One fixed finitely presented group has Sigma-zero-two-complete MF-radical membership
root: true
distinct_from:
  fixed-non-mf-radical-membership-undecidable: that gives first-level undecidability through an amenable free factor; this asks for FIN-hardness.
  mf-radical-membership-has-a-sigma2-upper-bound: that supplies the upper bound for every fixed presentation but no fixed-group hardness.
---

Construct one finitely presented group `U` and a computable word map `e |-> w_e`
such that

```text
e in FIN  iff  w_e in Res_MF(U).
```

By [[mf-radical-membership-has-a-sigma2-upper-bound]], this would make
`Res_MF(U)` a `Sigma^0_2`-complete set of words.  Equivalently, because

```text
w in Res_MF(U)  iff  w=1 in Q_MF(U),
```

the word problem of the fixed universal MF quotient `Q_MF(U)` would be
`Sigma^0_2`-complete.

## Attempts

The amenable-factor retraction gives undecidability only.  The active route is
to compress the FIN stable kernel while keeping the universal quotient MF.
