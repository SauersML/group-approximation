---
rg: 2
id: bs14-bounded-period-shadowing-proof
kind: route
title: Cut each long fourth-power orbit and shadow every segment by a periodic point
target: bs14-long-cycles-admit-bounded-period-shadowing
requires:
  - bs14-unitary-representations-are-periodic-cycle-packets
---

Use `bs14-unitary-representations-are-periodic-cycle-packets` and diagonalize
each packet monodromy.  It is enough to work on a multiplicity-one packet of
length `m`, with circle coordinates

```text
theta_j=4^j theta mod 1,                0<=j<m,
S e_j=exp(2 pi i theta_j)e_j,
```

and with `R` the cyclic shift, carrying one arbitrary scalar phase on its
closing edge.

If `m<=K`, make no change.  If `m>K`, put `b=ceil(m/K)` and partition the
cyclic list into `b` consecutive segments.  The segment lengths are at most
`K`, and

```text
b <= m/K+1 < 2m/K.                                    (BPS1)
```

Consider a segment of length `ell`, starting at the circle point `alpha`.
Choose an integer `q` nearest to `(4^ell-1)alpha` and put

```text
eta=q/(4^ell-1) mod 1.
```

Then `4^ell eta=eta mod 1`, and for `0<=j<ell`, circular distance satisfies

```text
d_T(4^j eta,4^j alpha)
 <= 4^j/(2(4^ell-1)).                                 (BPS2)
```

Replacing the segment labels by the exact periodic orbit of `eta` therefore
costs, in unnormalized Hilbert--Schmidt square,

```text
sum_(j=0)^(ell-1)
 |exp(2 pi i 4^j eta)-exp(2 pi i 4^j alpha)|^2
 <= pi^2 sum_(j=0)^(ell-1) 16^j/(4^ell-1)^2
 =  pi^2(4^ell+1)/(15(4^ell-1))
 <= pi^2/9.                                            (BPS3)
```

On each segment let the new `R` be the cyclic shift compatible with this
periodic orbit.  Keep every old shift edge internal to a segment and alter
only its closing edge.  Closing phases may be chosen arbitrarily; for
example, retain the original packet phase on one child segment and use phase
one on the others.  The exact relation `(BCT1)` holds on every child packet.
The old and new shifts differ on at most `b` unit basis vectors, so

```text
||R-R_K||_F^2 <= 4b <= 8m/K.                          (BPS4)
```

By `(BPS3)` and `(BPS1)`, the base-unitary cost on this packet is at most

```text
||S-S_K||_F^2 <= (pi^2/9)b <= 2pi^2 m/(9K).           (BPS5)
```

Sum `(BPS4)--(BPS5)` over the orthogonal scalar packets and divide by the
total dimension `d`.  This gives `(BCT2)`.  Every replacement eigenvalue has
order dividing `4^ell-1`, hence odd, and every new fourth-power orbit has
length dividing `ell<=K`.
