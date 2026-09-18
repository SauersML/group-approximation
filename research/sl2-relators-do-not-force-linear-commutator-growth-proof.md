---
rg: 2
id: sl2-relators-do-not-force-linear-commutator-growth-proof
kind: route
title: Exact affine action of the Wollmilchsau affine group on scaled grid vertices, a diagonal Q_8 quotient, and the 4 pi cone-point monodromy
target: sl2-relators-do-not-force-linear-commutator-growth
requires: []
---

Notation as in the claim. All ranks are over `Q` (equivalently `C`). For a permutation matrix `P`,
`moved(P)/2 <= rank(P - I) <= moved(P)`.

**Step 0: the origami.** Squares `g in Q_8`. The right neighbour of `g` is `ig` and the top
neighbour is `jg`. The four-edge loop around the lower-left corner of square `g` returns to `-g`,
so every vertex of `O` is a cone point of angle `4 pi` (4 cone points, genus 3). Right
multiplications `g -> g h` commute with `B, C`, so `Aut(O) >= Q_8`, and it equals `Q_8`
because the action is regular. The Veech group is `SL_2(Z)`: `affine.py` finds, for `A = S` and `A = T`,
8 affine maps (all lifts, a `Q_8`-torsor) by developing straight segments. So
`1 -> Q_8 -> Aff(O) -> SL_2(Z) -> 1`.

**Step 1: exact action on scaled vertices.** In `O_m` the grid vertices are the points with
coordinates in `(1/m) Z^2` relative to a cone point. An affine `f` maps cone points to cone points and
has derivative in `SL_2(Z)`, so it maps grid vertices to grid vertices and non-corner vertices
`V_m` to `V_m`. This gives an exact homomorphism `Aff(O) -> Sym(V_m)`. `affine.py` computes it with
exact rationals, an infinitesimal generic offset, and the consistency check over all squares. A small
square is identified with its lower-left vertex, and the 8 corner squares (whose lower-left vertex is a cone
point) are fixed by every `f`. The patch changes each `f` on at most 8 points per copy.

**Step 2: why a quotient is needed.** For every lift `S~` of `S`, `S~^4 in Q_8` is `-1` on `V_m`
(`split_test.py`, all 64 lift pairs, `rank(s^4 - I) = 140` at `m = 6`). This is a translation, so
its rank is `~ d/2`. Hence no choice of lifts on `X_m` alone gives bounded `SL_2(Z)` relators.

**Step 3: the diagonal quotient.** Let `Y = V_2` (24 points). `Aff(O)` acts exactly on it, and
`Q_8` acts freely (a translation acts freely on squares). On `V_m x Y` the diagonal action of `Aff(O)`
commutes with the diagonal `Q_8` up to conjugation inside `Q_8`. So `Aff(O)` acts on
`W = (V_m x Y)/Q_8` and `Q_8` acts trivially there. Any word in `s, t` that is trivial in
`SL_2(Z)` acts on `W` as an element of `Q_8`, hence as the identity. `tuple_q8.py` realizes `W`,
together with the 24 corner-square classes, as `X_m x (Y/Q_8)` through orbit representatives:
`F(p, o) = (tau^-1 F p, o')`, where `F y_o = tau y_(o')`. This is a permutation of
`X'' = X_m x {0,1,2}`, `d = 24 m^2`, and agrees with the honest action on `W`. `B, C` act on the first factor. A
relator word of length `l` deviates from its value on `W` only on the `<= 24 l` points whose
trajectory meets a corner square. So `rank(s^4 - I)` and `rank(s^2 (st)^-3 - I)` are bounded independently of
`m` (computed: 8 and 14).

**Step 4: conjugation relators.** For `p in V_m`, `f_S B f_S^(-1) p = p + A_S e_1 = p + e_2 = C p` unless the
unit step passes a cone point. The same holds for `f_T C f_T^(-1) p = p + (1,1)` against `B C p`
(the diagonal and the right-then-up path agree unless the far corner of the small square is a cone
point). Only boundedly many points per copy, near the 4 cone points, are affected. Computed ranks:
18, 24, 18, 18.

**Step 5: the commutator.** `B C p != C B p` only when the upper-right corner of the small square
`p` is a cone point: 8 squares per copy, paired by `-1`. So `rank([B,C] - I) = 4 N = 12`.

**Step 6: quadratic growth.** Fix `1 <= L <= m` and a cone point `x` in one copy. The loop
`w_L = b^L c^L b^-L c^-L` from the square `p` develops to the boundary of an `L x L` lattice
square of square-centres, and it never passes through a vertex. If `x` lies in its open interior, the
loop has winding `2 pi` around a point of angle `4 pi`, and lifts to a path ending on the other sheet,
so `w_L p != p`. Cone points sit at mutual lattice distance `>= m >= L`, so there is at most one inside. For each of the 2 sheets at
`x` there are `L^2` start squares `p` placing `x` inside. So `w_L` moves at least
`N * 4 * 2 L^2 = 24 L^2` points and `phi(L) >= 12 L^2`. `results.txt` gives exactly `12 L^2` for
`m in {4, 8, 12, 16, 24}` at `L in {1, 2, m/4, m/2, m}`.

**Step 7: conclusion.** The tuple `(B, C, S, T)` has every relator rank `<= 24`, and `phi(m) = 12 m^2`.
So `sup_m phi(m)/m = infinity` at fixed `k = 24`. QED.

**Calibration.** For the flat torus (one square, no cone point) the scaled square `(Z/m)^2` carries the
exact affine representation of `(Z/m)^2 x| SL_2(Z)` with `phi = 0`, matching the linear law for
near-commuting pairs. Step 6 is the only place where the cone point enters, and Step 2 is the only place
where `Aut(O) != 1` costs anything.
