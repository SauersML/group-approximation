---
rg: 2
id: non-hyperlinear-from-sl3-large-prime-collapse
kind: route
title: The SL3 pair at a prime at least 11 reaches the goal through the HNN reduction
target: non-hyperlinear-group
requires:
  - hnn-route-is-relative-commutant-collapse
  - sl3-large-prime-pair-relative-commutant-collapse
---

Instantiate `hnn-route-is-relative-commutant-collapse` at
`A = SL_3(Z[1/p])`, `C = SL_3(Z)`, `a_1 = h = diag(p, 1, 1/p)` for a prime
`p >= 11`:

```text
G_p = < SL_3(Z[1/p]), t | [t, SL_3(Z)] = 1 >,
```

finitely presented since `SL_3(Z[1/p])` is and `SL_3(Z)` is finitely
generated.  Co-density and properness are prime-generic (congruence subgroup
property, strong approximation, `h notin C`).  The reduction says `G_p` is
not hyperlinear as soon as `(RC3-p)` holds for the restrictions of its
hyperlinear approximations, which is `sl3-large-prime-pair-relative-commutant-collapse`.
The difference from `non-hyperlinear-from-sl3-relative-commutant-collapse`
is only the prime: at `p >= 11` the depth-free Atkin--Lehner bound empties
the `p`-divisible `Lambda`-exact sector, so this edge carries the sharpest
current reduction of the goal to `sl3-z-weakly-ucp-stable`.
