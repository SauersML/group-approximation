---
rg: 2
id: sl3z-incoherent-via-f2-by-free-subgroup
kind: route
title: An embedded F_2-by-free group would make SL_3(Z) incoherent by Kropholler–Walsh (dead route)
target: sl3z-is-incoherent
requires:
  - sl3z-contains-f2-by-free-subgroup
---

Kropholler–Walsh, *Incoherence and fibering of many free-by-free groups*,
arXiv:1910.09601. The abstract was read 2026-09-16 and the body was not. The
abstract states that they apply their criterion "to finite index subgroups of
`F_2 ⋊ F_n` to show incoherence of all such groups". The range of `n` was not
checked against the body; it must exclude `n = 1`, because free-by-cyclic
groups are coherent (Feighn–Handel, recalled). Take `n >= 2`.

So an embedded `F_2 x| F_m` with `m >= 2` contains a finitely generated
subgroup that is not finitely presented, and so does `SL_3(Z)`.

Dead for `SL_3(Z)`: its prerequisite `sl3z-contains-f2-by-free-subgroup` is
refuted by `sl3z-normal-f2-subgroups-have-virtually-cyclic-quotients`. A normal
`F_2` in a subgroup of `SL_3(Z)` has a finite or virtually cyclic quotient.

The authors of the general free-by-free incoherence statement
(Kropholler–Vidussi–Walsh, arXiv:2005.01202) withdrew it. For fibre rank
`n >= 3`, the only incoherence mechanism recorded in the graph is the
Euler-characteristic route `sl3z-incoherent-via-euler-fibered-subgroup`.
Whether the Kropholler–Walsh criterion covers particular groups with `n >= 3`
was not checked, since the body of arXiv:1910.09601 was not read.
