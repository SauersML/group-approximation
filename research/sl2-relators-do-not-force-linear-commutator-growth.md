---
rg: 2
id: sl2-relators-do-not-force-linear-commutator-growth
kind: claim
title: Rank-24 permutation tuples of Z^2 x| SL_2(Z) built from the scaled Eierlegende Wollmilchsau have rank([b^L,c^L]-I) = 12 L^2, so the SL_2(Z) relators do not force linear growth
artifacts:
  - experiments/origami-veech-phi-2026-09-17/perm.py
  - experiments/origami-veech-phi-2026-09-17/wms.py
  - experiments/origami-veech-phi-2026-09-17/scaled.py
  - experiments/origami-veech-phi-2026-09-17/affine.py
  - experiments/origami-veech-phi-2026-09-17/split_test.py
  - experiments/origami-veech-phi-2026-09-17/tuple_q8.py
  - experiments/origami-veech-phi-2026-09-17/search_small.py
  - experiments/origami-veech-phi-2026-09-17/results.txt
distinct_from:
  z2-commuting-pairs-are-not-bounded-rank-stable: that is a dislocation dipole for Z^2 alone, and its Burgers vectors are not SL_2(Z)-invariant; this is a cone-point defect whose monodromy is SL_2(Z)-invariant, and it carries a full rank-bounded tuple of Z^2 x| SL_2(Z).
  deligne-cover-bounded-rank-sector-tuples-have-bounded-dimension: that is the bounded-rank rung for the whole Deligne cover; this kills one sub-route to it, bounded-rank control of the long-root commutator growth through the SL_2(Z) relators alone.
---

**ESTABLISHED** (`sl2-relators-do-not-force-linear-commutator-growth-proof`). Unreviewed. The general-`m`
argument is geometric; `results.txt` certifies `m = 4, 8, 12, 16, 24` exactly.

**Setting.** `P = Z^2 x| SL_2(Z) = < b, c, s, t | [b,c], t b t^-1 b^-1, t c t^-1 (bc)^-1,
s b s^-1 c^-1, s c s^-1 b, s^4, s^2 (st)^-3 >`, where `S = [[0,-1],[1,0]]`, `T = [[1,1],[0,1]]` act on
`b = e_1`, `c = e_2`. This is the copy of `Z^2 x| SL_2(Z)` inside `SL_3(Z)` inside `Sp_6(Z)` used in
`deligne-cover-bounded-rank-sector-tuples-have-bounded-dimension`. Put `phi(L) = rank(rho([b^L, c^L]) - I)`.

**Theorem.** For every `m >= 2` there are permutation matrices `B, C, S, T` of size `d = 24 m^2` with

```text
rank(rho(r) - I) <= 24      for all seven relators r of P,
phi(L) = 12 L^2             for 1 <= L <= m     (proved: phi(L) >= 12 L^2; computed equal).
```

So no bound `phi(L) <= C(k) L` follows from the relators of `P`: at `k = 24`, `phi(m)/m = 12 m`.
The same holds for `phi` normalized by any `o(L^2)` rate. The answer to the wave-3 question "do the
`SL_2(Z)` relators force `rank([b^L,c^L] - I) <= C(k) L`?" is **no**.

**Construction.**
1. `O` is the Eierlegende Wollmilchsau: 8 unit squares labelled by `Q_8`, with `B, C` left
   multiplication by `i, j`. `[B,C]` is multiplication by `-1`, so `O` has 4 cone points of angle
   `4 pi`, and every square corner is one of them. Its Veech group is `SL_2(Z)` and `Aut(O) = Q_8`.
   The derivative gives `1 -> Q_8 -> Aff(O) -> SL_2(Z) -> 1`.
2. `O_m` subdivides every square into `m x m`. Affine maps permute the cone points and have integral
   derivative, so `Aff(O)` acts **exactly** on the non-corner grid vertices `V_m` (`8(m^2 - 1)`
   points), with `Q_8` acting freely. Small squares are identified with their lower-left vertex, and the 8
   corner squares are patched by the identity.
3. The extension does not split in the way needed: for every lift of `S` and `T`, `s^4` is the central
   `-1` in `Q_8`, which moves `d/2` points (`split_test.py`). The fix is a diagonal quotient: `Y = V_2`
   (24 points, free `Q_8`-action), `X'' = (X_m x Y) / Q_8`, with `N = 3` orbits. `Q_8` acts trivially on
   `X''`, so `Aff(O)` acts through `SL_2(Z)`. `B, C` act on the `X_m` factor.

**Mechanism.** Dislocations (the earlier obstruction) have Burgers vectors, which `SL_2(Z)` moves, so
they cannot survive the conjugation relators. A cone point of angle `4 pi` has monodromy "go to the
other sheet", which every affine map preserves. A lattice loop `[b^L, c^L]` around the cone point
ends on the other sheet, and `2 L^2` start squares per cone point see this (the area law saturated).

**Consequence.** Bounded-rank control of the unipotent sector of a rank-`k` tuple cannot come from
`Z^2 x| SL_2(Z)` relators. It must use relators of `Gamma_n` outside `P`, for example `e_31, e_32` in
`SL_3(Z)`, which do not normalize `<e_13, e_23>`. The origami surfaces above would then need an
`SL_3(Z)`-compatible affine structure. That is the next falsifiable step.
