---
rg: 2
id: regular-short-low-frequency-bs-source-hull-is-sublinear
kind: claim
title: A slow length-frequency cut makes the full BS source hull sublinear on the regular face
distinct_from:
  bs14-residual-invariant-hull-has-unbounded-packet-loss: that shows a rank-one source can have an arbitrarily large finite packet hull; this proves that after a joint length and R-frequency cut, the hull has vanishing relative dimension along a regular-character sequence.
  long-bs-packet-source-mass-is-frequency-small: that deletes source mass on moving long packets without taking any invariant hull; this combines it with a shrinking spectral band on the remaining short packets and then safely takes the whole BS hull.
  bs14-regular-character-forces-sublinear-fixed-source: that controls the exact R-fixed space; this treats approximate low-frequency sources and includes their full S-orbit hull.
---

**ESTABLISHED.**  Let `(R_n,S_n)` be exact finite-dimensional
`BS(1,4)` cores on `H_n`, `d_n=dim H_n`, whose characters converge to the
regular character.  Let `W_n:E_n -> H_n` be contractions satisfying

```text
f_n=d_n^(-1)||(R_n-1)W_n||_F^2 ->0.                  (SLH1)
```

Assume their long-packet mass obeys the already proved bound from
`long-bs-packet-source-mass-is-frequency-small`.  Then there are cutoffs

```text
M_n->infinity,                  delta_n->0             (SLH2)
```

and contractions

```text
W_n^good
 =P_(packet length <M_n) 1_(|R_n-1|<delta_n) W_n      (SLH3)
```

such that

```text
d_n^(-1)||W_n-W_n^good||_F^2 ->0,                    (SLH4)
```

while the full `(R_n,S_n)`-invariant hull `K_n` of `ran(W_n^good)` satisfies

```text
dim(K_n)/d_n ->0.                                     (SLH5)
```

The key finite-dimensional estimate is

```text
dim(K_n)
 <=M_n rank(1_(|R_n-1|<delta_n)).                    (SLH6)
```

Indeed, after diagonalizing every return monodromy, a scalar packet of
length `m<M_n` is an `m`-cycle.  Every `R_n` eigenvector which occurs in the
source generates under `S_n` at most that whole `m`-dimensional scalar
packet.  Summing over the low-frequency eigenvectors proves `(SLH6)`, even
when one source vector is spread across arbitrarily many return phases.

Regular-character convergence makes the spectral law of `R_n` converge to
Haar measure.  Therefore one may choose `delta_n->0` slowly enough that

```text
a_n=d_n^(-1)rank(1_(|R_n-1|<delta_n))->0,
f_n/delta_n^2->0.                                    (SLH7)
```

Then choose `M_n->infinity` still more slowly so that `M_na_n->0`.
Equation `(SLH6)` gives `(SLH5)`.  The high-frequency discarded source mass
is at most `f_n/delta_n^2`, while the long-packet mass is at most
`M_n^(-1)+2f_n^(1/3)`; this proves `(SLH4)`.

Thus the invariant-hull firewall is not fatal on the regular branch.  The
correct operation is not “short packet implies `M rank(W)`”; that statement
is false.  It is “short packet plus an ambient low-frequency spectral-rank
cut implies `M` times the spectral rank,” followed by a slow diagonal.

Because `U_1=S^2` and `U_2=RS` lie in the BS core, both forward exits of
`W_n^good` remain in `K_n`.  Hence cutting or rebuilding this entire hull
retains the cross-threshold source/exit data at `o(d_n)` cost rather than
splitting a native cell across the cutoff.
