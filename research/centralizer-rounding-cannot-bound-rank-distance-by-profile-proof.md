---
rg: 2
id: centralizer-rounding-cannot-bound-rank-distance-by-profile-proof
kind: route
title: The 2p-cycles of the kept word lie over a proper set of orbits that the other generator translates, so every commuting rounding must move them
target: centralizer-rounding-cannot-bound-rank-distance-by-profile
requires: []
---

Notation as in the claim. `p >= 5` is prime, `h = (p-1)/2`, `Omega = (Z/p)^2 x Z/2`, `n = 2p^2`, `P = (0,0)`, `Q = (0,h)`.
For permutations `x, y` of an `M`-set, `rank(x - y) = rank(x y^-1 - I) = M - #cycles(x y^-1)`. This is at
least half the number of points moved by `x y^-1`, and at most that number.

## 1. Distance and profile

Put `b0(x,e) = (x+e1, e)` and `c0(x,e) = (x+e2, e)`. These commute. `b b0^-1` is the transposition
of `(P+e1, 0)` and `(P+e1, 1)`, so `rank(b - b0) = 1`, and likewise `rank(c - c0) = 1`. Hence
`dist <= 1`. Lemma B of `near-exact-tuples-saturate-linear-conversion-defect-proof` then gives `rho <= 2`.

The direct argument is short. `rank(b^s - b0^s) <= s` and `rank(c^t - c0^t) <= t` by telescoping.
Moreover `rank([x,y] - [x0,y0]) <= 2 rank(x - x0) + 2 rank(y - y0)`, and `[b0^s, c0^t] = I`. So
`rank([b^s,c^t] - I) <= 2(s+t)`.

`crossframes.py` computes `rho = 2` exactly for `p = 11, 13, 17`, attained at `s = t = 1`. Only the
upper bound is used below.

## 2. The kept word

Fix a primitive `v = (v1, v2)` with `|v1| + |v2| <= p-1`, and let `B = b^v1 c^v2` (apply `c^v2` first).
Since `|v_i| < p` and `v != 0`, `v` is nonzero mod `p`.

**Base action.** On the base, `B` is the translation `x -> x + v`.

**Fibre action.** `B(x,e) = (x+v, e + phi(x))`, where `phi(x) = [x in D_Q] + [x in D_P] mod 2`.
- `c^v2` passes through the swap point `Q` exactly when `x` lies in `D_Q = Q - S_2`. Here `S_2` is the
  set of `|v2|` consecutive multiples of `e2` visited: `{0, ..., v2-1} e2` if `v2 >= 0`, and
  `{-1, ..., v2} e2` if `v2 < 0`.
- From `y = x + v2 e2`, `b^v1` passes through `P` exactly when `x` lies in `D_P = P - v2 e2 - S_1`,
  where `S_1` is the analogous set of `|v1|` consecutive multiples of `e1`.
- So `D_Q` consists of `|v2|` distinct points on the line `x1 = 0`, and `D_P` of `|v1|` distinct points
  on the line `x2 = -v2`. The points are distinct because each count is below `p`.

**Orbits.** Let `iota(x) = v1 x2 - v2 x1 in Z/p`. This is a nonzero linear functional whose kernel is
`<v>`. Hence the `B`-orbits on the base are the `p` level sets of `iota`, each of size `p`. Note that
`iota(x + e1) = iota(x) - v2` and `iota(x + e2) = iota(x) + v1`.

**Each orbit meets `D_Q` and `D_P` at most once.**
- On `D_Q`, `iota(0, q) = v1 q`, with `q` running over `|v2|` consecutive residues. If `v1 != 0` these
  values are distinct. If `v1 = 0`, primitivity gives `|v2| = 1`, so `D_Q` is a single point.
- On `D_P`, `iota(a, -v2) = -v1 v2 - v2 a`, with `a` running over `|v1|` consecutive residues. The same
  argument applies.

So `I_Q = iota(D_Q)` has exactly `|v2|` elements and `I_P = iota(D_P)` has exactly `|v1|`.

**Cycle structure.** Over the orbit `O = iota^-1(j)`, `B^p(x,e) = (x, e + sum over y in O of phi(y))`,
and the sum is `[j in I_Q] + [j in I_P] mod 2`. Hence `B` has one `2p`-cycle over `O` when `j` lies in
`J = I_P (symmetric difference) I_Q`, and two `p`-cycles over `O` otherwise. Write `M_B` for the union
of the `2p`-cycles of `B`. Then `M_B = iota^-1(J) x Z/2`.

**`J` is a nonempty proper subset of `Z/p`.** Properness: `|J| <= |v1| + |v2| <= p-1`. Nonemptiness:
- If `|v1| != |v2|` then `|I_P| != |I_Q|`, so `J` is nonempty.
- Otherwise primitivity forces `|v1| = |v2| = 1`, and we compute directly.
  - `D_Q` is `{Q}` if `v2 = 1`, and `{Q + e2}` if `v2 = -1`. So `I_Q` is `{v1 h}` or `{v1 (h+1)}`,
    which is one of `+-h, +-(h+1)`.
  - `D_P` is `{(0, -v2)}` if `v1 = 1`, and `{(1, -v2)}` if `v1 = -1`. So `I_P` is `{-v2}` or `{0}`,
    which lies in `{-1, 0, 1}`.
  - Since `2 <= h < h+1 <= p-2` for `p >= 5`, the two singletons differ, and `|J| = 2`.

## 3. Conjugators

Let `(b'', c'')` commute with `b''^v1 c''^v2 = B`. Then both `b''` and `c''` commute with `B`.

**Case `v1 != 0`.**
1. Put `theta = c c''^-1`. Then `theta B theta^-1 = c (c''^-1 B c'') c^-1 = c B c^-1`.
2. Conjugation carries cycles to cycles of the same length. So `theta(M_B)` is the union of the
   `2p`-cycles of `c B c^-1`, which is `c(M_B)`.
3. Since `iota(x + e2) = iota(x) + v1`, we have `c(M_B) = iota^-1(J + v1) x Z/2`.
4. `v1` generates `Z/p`. A nonempty proper subset of `Z/p` is not invariant under a generator, so
   `J + v1 != J`. The two sets have the same size, so there are `j in J \ (J + v1)` and
   `j' in (J + v1) \ J`.
5. Every point `z` of `M_B` over `j` has `theta(z) in c(M_B)`, which does not contain `z`. Every point
   `y` of `c(M_B)` over `j'` has `theta^-1(y) in M_B`, which does not contain `y`.
6. Hence `theta` moves at least `2p + 2p = 4p` points, and
   `rank(c'' - c) = rank(theta - I) >= 4p / 2 = 2p`.

**Case `v1 = 0`.** Then `v = (0, +-1)`. Use `theta = b b''^-1` instead: it conjugates `B` to `b B b^-1`,
whose `2p`-cycles are `b(M_B) = iota^-1(J - v2) x Z/2`. Since `v2 = +-1` generates `Z/p`, the same
argument gives `rank(b'' - b) >= 2p`.

**Part 3.** This is part 2 applied to the primitive vector `u` in place of `v`.

## 4. Remarks

- The bound uses only the conjugacy constraint `theta B theta^-1 = g B g^-1` with `g in {b, c}`. So it also
  covers a rounding in which a fibre bijection conjugates the row monodromies at the two ends of a band.
- It does not bound the distance: `(b0, c0)` changes both generators and costs 1.
- `crossframes.py p` recomputes `M_B` and `g(M_B)` for every primitive `v` with `|v|_1 <= p-1` (for
  `p = 11, 13, 17`). It confirms that the cycle lengths lie in `{p, 2p}`, that `M_B` is nonempty, and
  that `|M_B \ g M_B| >= 2p`.
