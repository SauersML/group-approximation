---
rg: 2
id: mikhailova-central-rope-left-right-wreath-proof
kind: route
title: Index the stable-letter conjugates by cosets and identify the Mikhailova coset set
target: mikhailova-central-rope-is-a-left-right-action-wreath
requires: []
---

In `<K,v | [v,L]=1>`, the conjugate `k v k^-1` depends only on the
coset `kL`.  Britton normal form gives no relations among conjugates
indexed by distinct cosets, so their normal closure is

```text
*_(K/L) <v_(kL)> ~= *_(K/L) Z.
```

Conjugation by `K` translates the coset index.  The quotient obtained by
killing all those free generators is `K`, and the original copy of `K`
splits it, proving the displayed semidirect-product decomposition.

For the Mikhailova subgroup

```text
M_H={(p,q) in F(X)xF(X): pbar=qbar},
```

the map

```text
(p,q)M_H |-> pbar qbar^(-1)
```

is well defined and bijects the coset set with `H`.  Under left
multiplication by `(r,s)`, its value becomes

```text
rbar (pbar qbar^(-1)) sbar^(-1),
```

which is precisely the combined left-right action.  The extra direct
`F` coordinate lies in both `K_0` and `L_0` and therefore disappears
from the coset set.
