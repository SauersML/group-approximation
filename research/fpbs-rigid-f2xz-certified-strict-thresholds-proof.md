---
rg: 2
id: fpbs-rigid-f2xz-certified-strict-thresholds-proof
kind: route
title: Star-stage Galton-Watson survival and a Busemann-weighted Schur test on cycle-avoiding walks, both checked exactly
target: fpbs-rigid-f2xz-certified-strict-thresholds
requires: []
artifacts:
  - experiments/fpbs-rigid-certificates-2026-09-17/star.c
  - experiments/fpbs-rigid-certificates-2026-09-17/certgw.py
  - experiments/fpbs-rigid-certificates-2026-09-17/rho2v.py
  - experiments/fpbs-rigid-certificates-2026-09-17/certschur.py
  - experiments/fpbs-rigid-certificates-2026-09-17/outputs.txt
---

**Setting.**
* `G = Cay(F_2 x Z, S_rig)`. Vertices are `(w,h)`, with `w in F_2` and `h in Z`.
* Edges:
  * vertical edges `(w,h) ~ (w,h+1)`;
  * ladder edges `(w,h) ~ (wl, h+d)`, for `l = a` with `d in D_a = {0,1,3}` and
    for `l = b` with `d in D_b = {0,1,4}`.

  The inverse letters carry `-D_l`. The fibre of `w` is `{w} x Z`.
* The graph is simple, 14-regular and transitive.
* `tau_p(x,y) = P_p(x <-> y)`, `theta(p) = P_p(|C(o)| = infinity)`, and
  `T_p` is the operator with kernel `tau_p`.

The proof has three steps. Step 1 is standard and Steps 2 and 3 are the
certificates:
1. `theta(p1) > 0` and `||T_(p2)||_{2->2} < infinity` with `p1 < p2` give
   `p_c <= p1 < p2 <= p_u`.
2. `theta(91/1000) > 0`.
3. `||T_p||_{2->2} < infinity` for all `p < 100/1093`.

Apply Step 1 with `p1 = 91/1000` and `p2 = 914/10000`.

## Step 1. From the two bounds to strict thresholds

Suppose `theta(p2) > 0` and there is a.s. a unique infinite cluster at `p2`. Then:
* `{o <-> infinity}` and `{x <-> infinity}` are increasing events.
* By Harris-FKG and uniqueness, `tau_(p2)(o,x) >= P(o <-> infinity, x <-> infinity) >= theta(p2)^2`
  for every `x`.
* So `sum_x tau_(p2)(o,x)^2 = infinity`.
* But `sum_x tau(o,x)^2 = ||T δ_o||^2 <= ||T||^2`.

Hence `||T_(p2)|| < infinity` and `theta(p2) >= theta(p1) > 0` force
nonuniqueness at `p2`. Uniqueness is monotone in `p` (Häggström-Peres 1999;
Schonmann 1999), so `p2 <= p_u`. Clearly `p_c <= p1`.

## Step 2. `theta(91/1000) > 0`

**Types.**
* Letters are indexed `0:a, 1:a^-1, 2:b, 3:b^-1`.
* An individual is a fibre `w = w' s` together with a finite nonempty set
  `G ⊂ Z` of heights. It is entered from its parent `w'` by the letter `s`, and
  every `(w,g)`, `g in G`, is known to lie in `C(o)`.
* The type is `(s, G - min G)`, restricted to `|G| <= K = 3` and
  `max G - min G < W = 6`. That makes `4 * 16 = 64` types.

**Stage of an individual.** Put `min G = 0`. Maintain a set `P` of heights known
to be in `C(o)` in fibre `w`, starting with `P = G`, and sets `C_t` for the three
child letters `t != s^-1`. Process a FIFO queue of discovered vertices.
* **A vertex `(w,h)`.**
  * Reveal the vertical edges to `h-1` and `h+1`. Skip one if the target is
    outside `[-A, W-1+A]` with `A = 4`, or is already in `P`.
  * Then, for each child letter `t` and `d in D_t`, reveal the ladder edge to
    `(wt, h+d)`, unless `h+d in C_t` already.
* **A child vertex `(wt,h')`.** Reveal its three back edges to `(w, h'-d)`,
  `d in D_t`, unless the target is outside the window or already in `P`.
* An open edge adds its target to `P` or `C_t` and to the queue.
* The stage stops when the queue is empty or when the revealed configuration has
  `p^i (1-p)^j < 10^-6` (`i` open and `j` closed revealed edges).

**Offspring.** At the end, each nonempty `C_t` gives a child `(wt, cap(C_t))`:
* first keep the heights `< min C_t + W`;
* then keep the `K` smallest of them.

**Why this is a Galton-Watson process.**
* *No edge is revealed twice inside a stage.* An edge is skipped when its far
  endpoint is already discovered, and each vertex is processed once. Suppose an
  edge was revealed closed from one endpoint, and its other endpoint is discovered
  later. When that endpoint is processed, the near end of the edge is already
  discovered, so the edge is skipped.
* *Stages own disjoint edges.* The stage of `w` reveals only two kinds of edge:
  * vertical edges inside fibre `w`;
  * ladder edges between `w` and its children `wt`, `t != s^-1`.

  Start at the fibre `a`, entered from `o = (e,0)` through the open edge
  `(e,0) ~ (a,0)` (probability `p`). The individuals then form a subtree of the
  Cayley tree of `F_2` rooted at `a` and pointing away from `e`. So different
  stages own disjoint edge sets, and none of them contains `(e,0) ~ (a,0)`.
* *The stopping rule is a stopping time.* It depends only on the revealed edges,
  so the stage outcome is a legitimate random variable of the owned edges.
* *The offspring law depends only on the type.* Left translation and translation
  of heights are automorphisms of `G`.

So the typed individuals form a multitype Galton-Watson process with bounded
offspring. Every discovered vertex lies in `C(o)`, so survival forces
`|C(o)| = infinity`. Hence
`theta(p) >= p * P(survival from type (a,{0}))`.

**Mean matrix.**
* `star.c` enumerates every branch of the stage exploration, for all 64 types.
  It records the number of leaves with given `(i,j)` and child type.
* In each output row, the weights `p^i (1-p)^j` of the leaves sum to 1.
* The caps `IMAX = 16` and `JMAX = 256` are never reached, because
  `0.091^6 < 10^-6` and `0.909^146 < 10^-6`. So the enumeration is exact.
* `certgw.py` forms `M(r,c) = sum count * p^i (1-p)^j` in exact rationals at
  `p = 91/1000`.

**Certificate.**
* The communicating class of `(a,{0})` consists of all 64 types.
* A float Perron vector is rounded up to a positive rational vector `v` with
  denominator `10^12`.
* The exact computation gives `min_k (Mv)_k / v_k = 1.016047...`, which is
  `>= 101/100`.
* By Collatz-Wielandt, `rho(M) >= 101/100 > 1`.

The mean matrix is irreducible with Perron root `> 1`, the offspring is bounded,
and the process is not singular. So the process survives with positive
probability (Harris; Athreya-Ney, Ch. V). In the periodic case, pass to `M^d` on
one cyclic class, which is primitive with root `rho^d > 1`. Hence
`theta(91/1000) > 0`.

## Step 3. `||T_p|| < infinity` for `p < 100/1093`

**Walk majorant.** For `ell = 5`:
* `W_n(x,y)` counts walks `x = x_0, ..., x_n = y` with `x_t != x_(t-j)` for
  `2 <= j <= ell`.
* Every self-avoiding path is such a walk, so `tau_p <= S_p := sum_n p^n SAW_n <= M_p := sum_n p^n W_n`.
* `SAW_n` is symmetric, since a reversed walk is a walk of the same kind.

**Schur test.** Let `h > 0` on vertices with `sum_y M_p(x,y) h(y) <= C h(x)`. Then:
* `S_p` is symmetric and `S_p <= M_p`, so `||S_p||_{2->2} <= C`.
* `tau_p <= S_p` entrywise gives `sum_x tau_p(o,x)^2 <= ||S_p δ_o||^2 <= C^2`.
* `T_p` is a nonnegative symmetric kernel dominated by `S_p`, so `||T_p|| <= ||S_p|| <= C`.

**Weights.**
* Fix an end `xi` of the 4-regular tree `F_2`.
* `beta(w)` is the Busemann function toward `xi`, and `t(w)` is the unique letter
  with `beta(w t(w)) = beta(w) - 1`.
* Put `h(w,z) = u^(-beta(w))`. Then
  `sum_y M_p(x,y) h(y) = h(x) * sum_n p^n sum_(walks from x) prod(step factors)`.
* The step factors are:
  * `1` for a vertical step;
  * `u` for the letter `t(w)`;
  * `1/u` for any of the other three letters.

**Transfer inequality.**
* A *state* `sigma` is a sequence of `ell - 1 = 4` steps whose partial
  products contain no nontrivial cycle. There are 29974 states.
* A transition appends a step `g` whose suffixes of length `2..5` are not the
  identity, and drops the oldest step.
* For `c : states x letters -> (0, infinity)` define

  ```text
  F(c)(sigma,t) = sum over allowed g of
      c(sigma',t)                                 if g vertical,
      (1/u) c(sigma', l^-1)                       if g has letter l != t,
      u * max_{t' != l^-1} c(sigma',t')           if g has letter l = t.
  ```

  After a step away from `xi` with letter `l`, the new toward-letter is `l^-1`.
  After a step toward `xi`, it is some letter other than `l^-1`.
* By induction on `k`, if `F(c) <= lambda c` then the weighted sum over the
  continuations of length `k` from a vertex in state `(sigma,t)` is at most
  `lambda^k c(sigma,t) / min c`.
* The first four steps of a walk contribute at most `(14u)^4`.
* Hence `sum_y M_p(x,y) h(y) <= h(x) * const * sum_n (p lambda)^n`, which is
  finite when `p lambda < 1`.

**Certificate.**
* `rho2v.py` builds the states and transitions and power-iterates `F` in floats
  with `u = 1732/1000`.
* `certschur.py` rounds `c` up to integers `ci = ceil(10^9 c) + 1 >= 1`. It then
  computes `out = UN*UD*F(ci)` exactly as an integer vector, with
  `u = UN/UD = 1732/1000`. It then checks `100 * out <= 1093 * UN*UD * ci`
  entrywise in Python integers.
* There is no int64 overflow: each entry is a sum of at most 14 terms, each at
  most `1732^2 (10^9+1) < 4 * 10^15`.
* Result: exact max ratio `10.918218666879...`, which is `<= 1093/100`. True.

So `||T_p|| < infinity` for `p < 100/1093 = 0.091491...`, in particular at
`p2 = 914/10000`, where `p2 * 1093/100 = 0.999002 < 1`.

**Calibration of the program.**
* With `ell = 1` (no memory, `u = sqrt 3`) it returns `2 + 6 sqrt 3 = ||A||`.
* With `ell = 2` it returns `11.2352`, the root of `lambda + 13/lambda = 2 + 6 sqrt 3`
  predicted by the Ihara formula for non-backtracking walks.
* Values for larger `ell`, as upper bounds `1/lambda` on the certified `p` range:

  | `ell` | `1/lambda` |
  |---|---|
  | 3 | 0.0904 |
  | 4 | 0.091153 |
  | 5 | 0.091590 |

## Reproduction

```text
gcc -O2 -o star star.c -lm
./star 91 1000 6 3 4 1e-6 > st91.txt           # 165373 lines, sha256 b0a83e63...
python3 certgw.py st91.txt 91/1000 101/100      # "... certifies rho(M) >= 101/100 : True"
python3 rho2v.py 5                               # float lambda 10.91822 at u = sqrt 3
python3 certschur.py 5 1732/1000 300 1732/1000 1093/100   # "... <= lam 1093/100 : True"
```

Recorded outputs are in `experiments/fpbs-rigid-certificates-2026-09-17/outputs.txt`.
Verification tier: exact rational and integer certificates, produced by programs
in the artifact directory, plus the standard theorems cited above. Nobody has
independently re-implemented them.
