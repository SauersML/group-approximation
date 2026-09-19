---
rg: 2
id: pure-cycle-surgery-rate-contains-quantitative-z2-repair
kind: claim
title: A pure K-delta cycle-surgery rate already contains a stronger quantitative Z2 repair theorem
distinct_from:
  flexible-bs-cycle-surgery-absorbs-exact-coboundaries: that proves qualitative flexible absorption and the pure rate on long base cycles; this isolates why the same pure rate on every packet does not follow from orbit cutting.
  bs14-full-commutant-finite-period-preconditioner: that quantizes return monodromy independently and then pays a KM inverse; this permits the repaired core and gauge to depend jointly on the almost-commuting pair.
---

Suppose one strengthened `(FCS3)` to **all** exact BS packets, including
length-one packets, with

```text
||R-R_0||_2+||S-S_0||_2+||c-c_0||_2
 <= C(K delta+K^(-1/2)),                              (PCZ1)
```

where `c_0 in {R_0,S_0}'`.  Put `S=1`, let `R` and `c` be arbitrary
unitaries, and set `delta=||[R,c]||_2`.  This is an exact length-one
`BS(1,4)` packet, and `(PCZ1)` produces commuting unitaries `R_0,c_0` with
the same bound.  Optimizing at `K` of order `delta^(-2/3)` would give

```text
||R-R_0||_2+||c-c_0||_2 <= C' delta^(1/3).            (PCZ2)
```

Thus the proposed pure all-packet rate contains a quantitative normalized-HS
stability theorem for `Z^2`; it is not a consequence of cutting long
fourth-power orbits.  The currently imported elementary theorem of Glebsky
gives the weaker bound `30 delta^(1/9)`.  This does not refute `(PCZ1)`, but
it identifies the extra theorem needed to assert it.

The valid unconditional replacement is `(FCP6)` in
`flexible-bs-cycle-surgery-proof`: the long packets contribute
`C(K delta+K^(-1/2))`, while return monodromy on the short packets contributes
`C(2K delta)^(1/9)`.  That is already enough for a dimension-free qualitative
modulus.
