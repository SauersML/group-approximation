---
rg: 2
id: fournier-facio-dimension-at-infinity-sharpness-proof
kind: route
title: Splice the bilateral shift into signed-square finite cycles
target: fournier-facio-dimension-at-infinity-escape-is-sharp
requires: []
---

Let `D={k|k|:k in Z}`.  The number of points of `D` in any integer interval
of length `L` is at most `2 sqrt(L)+2`: gaps between consecutive nonnegative
squares, and between consecutive negative squares, increase monotonically,
so the densest interval is within the same bound as an interval meeting the
origin.  For a translation-invariant mean `mu`, averaging the translates of
`1_D` over an interval of length `L` gives

```text
mu(D)
 = mu((1/L) sum_{j=0}^{L-1} 1_(D-j))
 <= (2 sqrt(L)+2)/L.
```

Letting `L` tend to infinity proves `mu(D)=0`; translations of `D` are null
as well.

Set `d_k=k|k|` and `I_k=[d_k,d_(k+1)-1]`.  Define the permutation `m` by
ordinary translation inside each `I_k` and by sending its right endpoint
back to `d_k`.  The exceptional endpoint set is `E={d_(k+1)-1:k in Z}`, a
translate of `D`, so `mu(E)=0`.  The permutation `m` and translation have
the same inverse image of every subset modulo `E`; translation invariance
therefore gives `m`-invariance of `mu`.  If `M` and `T` are the corresponding
permutation unitaries, their image vectors agree off `E` and are orthogonal
on `E`, proving `(FDIS2)`.

The powers of one unitary form an exact representation.  On a cycle of
length `ell`, `M^n` has a fixed point exactly when `ell` divides `n`.  Since
`|I_k|=d_(k+1)-d_k` tends to infinity in both directions, only finitely many
cycles have length at most `|n|`.  Translation-invariant means vanish on
finite sets, so the diagonal coefficient of every nonzero power has charged
integral zero.  The same observation gives `(FDIS4)`.  Finally the diagonal
of every compact operator belongs to `c_0(Z)`, which every translation-
invariant free mean annihilates, so `phi_mu` is purely singular.
