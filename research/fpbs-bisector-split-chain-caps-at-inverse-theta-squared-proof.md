---
rg: 2
id: fpbs-bisector-split-chain-caps-at-inverse-theta-squared-proof
kind: route
title: On a straight path every dual circuit around the cut crosses the half-axis on the U^+ side, so the half-plane event A^L is trivial on the adjacent two-run pattern and the chain's exact output is 1/(q(S^-)q(S^+)); disjoint finger tubes that reach over the cut without surrounding it cap Theta^- by (1-c_0) per dyadic scale
target: fpbs-bisector-split-chain-caps-at-inverse-theta-squared
requires:
  - fpbs-planar-spine-multirun-decorrelation-by-dual-circuits
  - fpbs-path-bridge-ratio-untilted-coverage-decorrelation
---

Notation as in the target and in
`fpbs-planar-spine-multirun-decorrelation-by-dual-circuits-proof`, whose
Lemma 1.1 (planar duality) and Steps 1-3 we use. The path is straight:
`x_i = (i-k+1, 0)`, the cut is `e_k = (0,0)(1,0)`,
`U^- = {(a,0) : a <= 0}` and `U^+ = {(a,0) : a >= 1}` (restricted to the path).
Dual edges are identified with their midpoints `m = (a,y)`.

## 0. The bisector on a straight path

**Lemma 0.1.** `L = {m : a < 1/2}` and `R = {m : a > 1/2}`. Dual edges with
`a = 1/2` lie in neither set.

*Proof.* Take `m = (a,y)` with `a < 1/2`. If `a >= 0`, then
`d(m,U^-) = sqrt(a^2+y^2)`, which is less than
`sqrt((1-a)^2+y^2) = d(m,U^+)`. If `a < 0`, then `d(m,U^-) <= sqrt(1/4+y^2)`,
because `U^-` contains the integer points nearest to `a` (the path is long,
and near its ends the claim holds a fortiori). Also
`d(m,U^+) >= sqrt((1-a)^2+y^2) >= sqrt(9/4+y^2)` when `a <= -1/2`. So
`m in L`. The case `a > 1/2` follows by the reflection `a -> 1-a`, which
swaps `U^-` and `U^+`. `□`

(If the path is finite and `m` lies beyond its left end, `d(m,U^-)` is the
distance to `x_0`. Then `d(m,U^-) < d(m,U^+)` still holds, because
`x_0` is closer to `m` than every point of `U^+`. The same holds at the right end.)

## 1. What a Step-4 refinement can and cannot do

Steps 1-3 of the source proof give, for every pattern `S`,

```text
K(S) <= P_S(A^L) P_S(B^R) / ( q(S^-) q(S^+) ) <= 1 / (Theta^- Theta^+).       (1.1)
```

Step 4 there, and any outermost-circuit or RSW-annulus variant, proves
lower bounds `Theta^± >= T^±`. It then concludes `K <= 1/(T^- T^+)`. Since
`T^± <= Theta^±`, the conclusion of any such argument is at least
`1/(Theta^- Theta^+)`. So an **upper bound** on `Theta^±` is an obstruction
to every refinement of Step 4 at once. Theorems A and B are such upper
bounds, on explicit patterns.

## 2. Theorem A

Let `S = {e_{k-1}, e_{k+1}}`, where `e_{k-1} = (-1,0)(0,0)` and
`e_{k+1} = (1,0)(2,0)`. So `S^- = {e_{k-1}}`, `S^+ = {e_{k+1}}`,
`V(S^-) = {(-1,0),(0,0)}` and `V(S^+) = {(1,0),(2,0)}`.

**Lemma 2.1.** Every dual circuit `gamma` surrounding `(0,0)` contains a
dual edge with midpoint `(i+1/2, 0)` for some `i >= 0`. In particular
`gamma` is not contained in `L`. Symmetrically, every dual circuit
surrounding `(1,0)` contains a dual edge with midpoint `(i+1/2,0)`, `i <= 0`,
and is not contained in `R`.

*Proof.* The ray `{(t,0) : t >= 0}` starts inside `gamma` and is unbounded,
so it meets `gamma`. Dual edges lie on the lines `a in Z + 1/2` or
`y in Z + 1/2`. The ray lies on `y = 0`, so it meets `gamma` only in vertical
dual edges, at their midpoints `(i+1/2, 0)`, `i >= 0`. Those have first
coordinate `>= 1/2`, so they are not in `L` (Lemma 0.1). The second
statement follows by reflection. `□`

**Proof of Theorem A.** *Step 1 is trivial.* Under `P_S`, the dual of
`e_{k-1}` is never open. By Lemma 1.1 of the source, a dual-open circuit
surrounding `(-1,0)` also surrounds `(0,0)`. By Lemma 2.1 no such circuit
lies in `L`. So `A^L` holds `P_S`-almost surely, and likewise `B^R`. Hence
`P_S(A^L) = P_S(B^R) = 1`, and Step 1 yields only `q(S) <= 1`.

*`Theta^- = q(S^-)`.* Under `P_{S^-}`, every dual-open circuit surrounding a
vertex of `V(S^-)` surrounds `(0,0)` (same argument), so by Lemma 2.1 it is
not contained in `L`. Thus `D^- = A` `P_{S^-}`-almost surely, and
`Theta^- = P_{S^-}(A) = q(S^-)`. Likewise `Theta^+ = q(S^+)`.

*Size.* `p' q(S^-) = P(e_{k-1} ⊆ Z)`. This is at most
`P((0,0) in the infinite cluster) = theta`. So `q(S^±) <= theta/p'`, and

```text
1/(Theta^- Theta^+) = 1/(q(S^-) q(S^+)) >= p'^2/theta^2.
```

*Truth.* `S` has one run on each side, so Theorem 2 of
`fpbs-path-bridge-ratio-untilted-coverage-decorrelation` gives
`K(S) <= 2/theta`. By Section 1, every refinement of Step 4 outputs at
least `p'^2/theta^2` here. That exceeds the truth by a factor of at least
`p'^2/(2 theta)`, which tends to infinity as `p' -> 1/2`. `□`

**Remark (what is lost).** Here `q(S)` equals
`P_S(no dual-open circuit surrounds (0,0) or (1,0))`, the probability of one
arm from the cut region to infinity, of order `theta`. Step 1 replaces it
by `P(A^L) P(B^R) = 1`, discarding exactly that one shared arm. Steps 2-3
then divide by `q(S^-) q(S^+)`, the cost of two arms. That is the whole
`1/theta` gap between `theta^{-2}` and `theta^{-1}`. It is located in Step 1
and is independent of Step 4.

## 3. Theorem B (finger circuits)

Fix an integer `b >= 4`. Let `S^-_J = {f_j : 1 <= j <= J}`, with
`f_j = (-b^j,0)(-b^j+1,0)`, and let `S^+_J` be its mirror image under
`a -> 1-a`. The runs are single edges and pairwise non-adjacent.

**Near-critical RSW (black box).** The dual measure is Bernoulli(`1-p'`)
with `1-p' < 1/2`. Let `L(p')` be Kesten's characteristic length (Kesten,
*Scaling relations for 2D percolation*, 1987; see Nolin, *Near-critical
percolation in two dimensions*, EJP 2008, Section 1.3). For every
`lambda >= 1` there is `delta(lambda) > 0` such that for every `p' in (1/2, 3/4]`,
every `n <= L(p')` and every `n x lambda n` rectangle, the dual-open
long-way crossing has probability at least `delta(lambda)`. For small `n`
this holds trivially, since `1-p' >= 1/4`.

**Tubes.** For `r = b^j >= 32`, put `w = r/16` and let `Pi_r` be the closed
polygon

```text
(-3r/2,-r/2) -> (-3r/2, r/2) -> (r, r/2) -> (r, r/4) -> (-r/2, r/4) -> (-r/2,-r/2) -> (-3r/2,-r/2).
```

Let `T_r` be the union of the six closed rectangles obtained by thickening
each side of `Pi_r` by `w` on both sides and extending it by `w` past both
endpoints. Let `F_r` be the event that the dual-open edges inside `T_r`
contain a circuit which winds once around `Pi_r`, that is, which separates
the bounded complementary region of `T_r` from infinity.

**Lemma 3.1.**

1. Every circuit in `F_r` surrounds both endpoints of `f_j`. It contains a
   dual edge with midpoint `a > 1/2`, so it is not contained in `L`. (It
   does not surround `(0,0)`, but that is not needed.)
2. `T_r` contains the dual of no edge of `S^-_J`.
3. For `r <= L(p')/3`, `P_{S^-_J}(F_r) >= c_0 := delta(42)^6`.
4. For `r' >= 4 r`, `T_r ∩ T_{r'} = ∅`.

*Proof.*

1. The bounded region of `R^2 \ T_r` contains the box
   `(-3r/2+w, -r/2-w) x (-r/2+w, r/4-w)`, which contains `(-r,0)` and
   `(-r+1,0)`. A circuit in `F_r` separates this region from infinity. It
   also meets the side of `T_r` at `a in [r-w, r+w]`, where `r - w > 1/2`.
2. The axis `y = 0` meets `T_r` only in `a in [-3r/2-w, -3r/2+w]` and
   `a in [-r/2-w, -r/2+w]`. The duals of `S^-_J` sit at `a = -b^i + 1/2`.
   These values are `>= -r/4 + 1/2` for `i < j`, `= -r+1/2` for `i = j`, and
   `<= -4r+1/2` for `i > j`. None lies in those two windows.
3. By 2, the marginal of `P_{S^-_J}` on `T_r` is Bernoulli(`1-p'`). Each of
   the six rectangles has width `2w` and length at most `5r/2 + 2w`, so its
   aspect ratio is at most `42`, and its long side is at most `3r <= L(p')`.
   Its long-way crossing has probability at least `delta(42)`. Consecutive
   rectangles overlap in a `2w x 2w` corner square, which one crossing
   traverses horizontally and the other vertically, so the two crossings
   meet. The six crossings together contain a circuit of `F_r`. The
   crossing events are increasing in the dual-open set, and Harris gives
   `P(F_r) >= delta(42)^6`.
4. Let `R' = r' >= 4r`. Every point of `T_{R'}` satisfies `a <= -7R'/16`,
   or `|y| >= 3R'/16`, or `a >= 15R'/16` (check the six sides). But
   `T_r ⊆ [-3r/2-w, r+w] x [-r/2-w, r/2+w]`, and
   `3r/2 + w < 7r/4 <= 7R'/16`, `r/2 + w < 3r/4 <= 3R'/16`, and
   `r + w < 15 R'/16`. `□`

**Proof of Theorem B.** Let `J_* = {j <= J : 32 <= b^j <= L(p')/3}`. Then
`c_1 = 1/3` in the statement. By Lemma 3.1(1), each `F_{b^j}` with
`j in J_*` produces a dual-open circuit which surrounds a vertex of
`V(S^-_J)` and is not contained in `L`. So `D^- ⊆ ∩_{j in J_*} F_{b^j}^c`.
By Lemma 3.1(4) the tubes are pairwise disjoint, since `b >= 4`. So the
events `F_{b^j}` are independent under the product measure `P_{S^-_J}`, and

```text
Theta^- = P_{S^-_J}(D^-) <= prod_{j in J_*} (1 - P(F_{b^j})) <= (1 - c_0)^{|J_*|}.
```

The same holds for `Theta^+` by reflection. By Section 1, every refinement
of Step 4 outputs at least `(1-c_0)^{-2|J_*|}` on `S_J`. For `J >= log_b L(p')`,
`|J_*| >= log_b(L(p')/96) - 1`, so this output is at least
`c(b) L(p')^kappa` with `kappa = 2 log(1/(1-c_0))/log b`. Kesten's
`L(p') -> infinity` as `p' -> 1/2` then gives the claim. `□`

**Remark (why the truth need not pay this).** A finger circuit around
`f_j` also stops `f_j` from reaching infinity. So `q(S)`, `q(S^-)` and
`q(S^+)` all carry a "no finger at scale `b^j`" factor, and it cancels in
`K`. The chain keeps it only in the denominator. The reason is that `A^L`
in Step 1 cannot see circuits that leave `L`. So the multiscale loss is
located in Step 1 as well.

A matching rigorous lower bound, of the form `Theta^- >= c theta (1-c'_0)^{J}`,
would need quasi-independence of arm events and finger events (arm
separation). It is not attempted here. The combination of Theorems A and B
into `Theta^- <= C theta (1-c_0)^{|J_*|}` would also need it. What is proved
is `Theta^- <= min(theta/p', (1-c_0)^{|J_*|})` when `e_{k-1}` is added to
`S^-_J`. Then `(0,0) in V(S^-)`, and Lemma 2.1 gives
`D^- ⊆ {(0,0) in an infinite cluster}`.

## 4. Numerics for the true `K`

`experiments/fpbs-dyadic-multirun-2026-09-18/dyadic.c` samples critical
bond percolation (`p = 1/2`) in `[-M,M]^2`, with the target `∂B_M` in place
of infinity. This is the standard finite-size proxy for `p' > 1/2` with
`L(p') ≍ M`. It holds out the pattern edges
`(-b^j,0)(-b^j+1,0)` and `(b^j,0)(b^j+1,0)`, for `0 <= j < J`, and decides
`q(S)`, `q(S^-)` and `q(S^+)` for all `J` from the same sample, on the
contracted graph of bulk clusters. So `K = qS/(qA qB)` has correlated,
small errors. The level `J = 1` is Theorem A's pattern. The results are in
`results.txt`. In every run `K * theta_proxy` lies in `[0.78, 0.85]` and
decreases slightly with `J`. So the true `K` on these multiscale patterns
is `≍ 1/theta`, while by Theorems A and B the chain's exact output is at
least `theta^{-2}`, respectively `L^kappa`.

## 5. Consequence for the gate

In `fpbs-spine-increment-activation-gate`, `K <= C theta^{-gamma}` with
`gamma < 36/5` suffices on `Z^2`, because `theta ~ (p'-1/2)^{5/36}`. So
Theorem A alone does not kill the chain *for the gate*. What remains is
the uniform statement `Theta^± >= c theta^{gamma/2}` over patterns, with
`gamma < 36/5`. Theorem B shows that any proof of it must pay a constant
factor per dyadic scale for fingers. The chain survives for the gate
exactly when that per-scale cost is small against the scale exponent of
`theta`. That is the open quantitative step recorded in the target.
