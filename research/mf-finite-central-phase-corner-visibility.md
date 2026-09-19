---
rg: 2
id: mf-finite-central-phase-corner-visibility
kind: claim
title: A finite central phase relation is maximally visible in one spectral corner
distinct_from:
  mf-antipodal-sign-corner-visibility: That is the order-two sign case and uses the formalized antipodal inequality; this treats every finite order and uses the exact trace identity on a nontrivial central-character corner.
  mf-finite-normal-tracially-visible: That makes elements of the finite normal subgroup itself visible; here the visible element may have infinite order and lie outside the finite central subgroup.
  mf-invariant-corner-visibility: That open claim asks for an invariant corner for every nontrivial element of every weak-MF group; this supplies one under a finite central phase-conjugacy relation.
---

Let `G` be a countable weak-MF group.  Suppose that `z` is a nontrivial
central element of finite order and that `g,s in G` satisfy

```text
s g s^(-1) = z g.                                                (FCP1)
```

Then `g` is maximally tracially visible: on every prescribed finite window
and at arbitrarily small operator-norm multiplicative defect there are matrix
models with

```text
tr(model(g)) -> 0,
||model(g)-1||_(2,norm)^2 -> 2.
```

More precisely, any faithful norm-corona representation of `G` has a nonzero
`G`-invariant spectral corner of `z` on which the compressed image of `g` has
trace zero.  Thus this is an exact finite-order fragment of
`mf-invariant-corner-visibility`, with visibility constant `1`.  The order of
`g` is unrestricted.

