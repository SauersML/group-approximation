---
rg: 2
id: atlas-q14-relative-chart-rank-correction
kind: claim
title: Vanishing q14 rank defect can be corrected exactly while preserving both repeated-natural Atlas chart types
distinct_from:
  atlas-q14-rank-centralizer-projection: that supplies an explicit linear correction but loses the square-zero and full-chart conditions; this uses flexible finite-algebra rank stability and marginal tuning to preserve both full chart types.
  atlas-rank-stability-literature-fence: that says published theorems do not synchronize the whole Atlas graph of groups; this proves the one q14 V4 bridge needed before the remaining thirteen fillings.
  atlas-left-ideal-rank-nonwandering: that concerns the twelve packet fillings and collision after q14; this removes q14 from the residual list at flexible rank cost but does not solve those thirteen residuals.
---

ESTABLISHED.  Let `rho_(1,n),rho_(2,n)` be two exact repeated-natural
`A8=GL_4(F2)` charts on `E_n=F2^(4m_n)`.  Let `x_n,y_n` be the two marked
transvections occurring in q14 and suppose

```text
rank((x_n y_n)^2-1)/dim(E_n) ->0.                    (QRC1)
```

After changing dimension by `o(dim E_n)`, there are exact repeated-natural
charts `rho'_(1,n),rho'_(2,n)` such that

```text
[rho'_(1,n)(t23),rho'_(2,n)(t23)]=1                 (QRC2)
```

and every fixed chart element changes by normalized rank `o(1)`.  Therefore
every fixed mixed word changes by normalized rank `o(1)`.  In particular,
any literal fourteen-residual Atlas rank microstate can be replaced by one
with q14 exact and the other thirteen residuals still tending to zero.

### Proof

Write `x_n=1+N_n`, `y_n=1+M_n`.  The two nilpotents square to zero and have
rank `m_n`.  By `atlas-q14-rank-centralizer-projection`, `(QRC1)` is exactly
the statement that `[N_n,M_n]` has normalized rank tending to zero.

Apply Bauer--Blachar--Greenfeld Theorem 5.1, recorded in
`atlas-rank-stability-literature-fence`, to the four-dimensional algebra

```text
F2<r,s>/(r^2,s^2,rs-sr).                              (QRC3)
```

Flexible rank stability gives, on dimensions `d_n'=4m_n+o(m_n)`, exact
commuting square-zero maps `N_n^0,M_n^0`, each at rank distance `o(m_n)`
from the corresponding zero-padded original map.  Their dimensions and
ranks are consequently

```text
d_n'=4m_n+o(m_n),
rank N_n^0=m_n+o(m_n),
rank M_n^0=m_n+o(m_n).                               (QRC4)
```

Tune the two marginal ranks using only `o(m_n)` extra exact modules for
`(QRC3)`.  A two-dimensional block with `(r,s)=(J_2,0)` raises only the
first rank; `(0,J_2)` raises only the second.  After equalizing the ranks,
one-dimensional trivial blocks increase dimension without rank, while
blocks `(J_2,J_2)` of dimension two (and, for the parity case, dimension
three after adjoining one trivial vector) increase both ranks.  Since all
discrepancies in `(QRC4)` are `o(m_n)`, this produces an exact commuting pair
`N_n^1,M_n^1` on dimension `4l_n`, with

```text
rank N_n^1=rank M_n^1=l_n,                            (QRC5)
```

still at stable rank distance `o(m_n)` from the originals.

A square-zero map on `4l_n`-space of rank `l_n` has Jordan type
`J_2^(l_n) direct_sum J_1^(2l_n)`, exactly the type of the marked
transvection on `V^(l_n)`.  Choose repeated-natural extensions of the two
original full charts to the tuned dimension.  By
`square-zero-near-conjugacy-in-rank`, there are basis changes `S_(i,n)` with
`rank(S_(i,n)-1)=o(m_n)` which carry their marked transvections to
`N_n^1,M_n^1`.  Conjugating the entire charts by these basis changes gives
`rho'_(i,n)`.  The marked elements commute, every chart element changes by
rank at most twice `rank(S_(i,n)-1)` plus the `o(m_n)` padding, and fixed
mixed words follow by telescoping.
