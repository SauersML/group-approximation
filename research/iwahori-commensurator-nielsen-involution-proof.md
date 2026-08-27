---
rg: 2
id: iwahori-commensurator-nielsen-involution-proof
kind: route
title: Compute the commensurator relative to the inner Iwahori conjugacy
target: iwahori-commensurator-nielsen-involution
requires: []
---

Work in `PSL_2(Z)` and choose the usual matrices

```text
S = [[0,-1],[1,0]],
T = [[1, 1],[0,1]],
D = diag(sqrt(2),1/sqrt(2)).
```

Thus `a=[S]`, `u=[T]` (the sign difference from `ab` in `SL_2` disappears
projectively), and the involutory Iwahori generator from the standard
coordinates is represented by

```text
e = [[1,-1],[2,-1]],            e^2=-I.
```

Conjugation by `D` is the commensuration `sigma`.  Direct multiplication
gives

```text
D T D^(-1) = T^2,
D e D^(-1) = [[1,-2],[1,-1]].
```

Conjugation by `S` sends the upper Iwahori subgroup to the lower one, so
`iota=Ad([S])`.  Applying `iota^(-1)` to the preceding two matrices gives,
up to the central sign,

```text
S^(-1) T^2 S
  = [[-1,0],[2,-1]]
  = T^(-1)e,

S^(-1) [[1,-2],[1,-1]] S
  = [[-1,-1],[2,1]]
  = T^(-1)eT.
```

Hence in `PSL_2(Z)`

```text
alpha(u)=u^(-1)e,
alpha(e)=u^(-1)e u.
```

Since `e^2=1` projectively, the formulas themselves prove involutivity:

```text
alpha^2(u)
 = alpha(u)^(-1) alpha(e)
 = (u^(-1)e)^(-1)(u^(-1)e u)
 = e u u^(-1)e u
 = u,

alpha^2(e)
 = alpha(u)^(-1) alpha(e) alpha(u)
 = e u (u^(-1)e u)(u^(-1)e)
 = e.
```

The pair `(u,e)` generates `Bbar_+ ~= Z*C_2`, so `alpha^2=id` on the whole
subgroup.

Finally `sigma=iota o alpha`.  If a representation of `Bbar_-` extends to
`Kbar`, pulling it back by `iota` gives a representation of `Bbar_+` which
still extends to `Kbar`, because `iota` is inner in `Kbar`.  Pulling it back
instead by `sigma` is exactly the `alpha`-twist of that same restriction.
Thus the two opposite extension loci are `E` and `alpha^*E`, as claimed.
