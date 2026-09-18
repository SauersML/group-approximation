# Zero-free test of (ZG) on the cycle-rich Cayley graph T_3 box K_2 (2026-09-17)

Worker `swarm-0917-w8-w8-bs-break`, calibration lane. This is the first killing
test proposed in `fpbs-connectivity-polynomials-zero-free-around-criticality`:
exact `a_(n,R)(z)` on a small nonamenable Cayley graph with overlapping cycles,
for small `n` and growing `R`. The code is in
`experiments/fpbs-zg-ladder-zeros-2026-09-17/`.

## 1. The graph and the exact reduction

`G = T_3 box K_2` is the Cayley graph of `(Z/2*Z/2*Z/2) x Z/2` with its four
standard involutions. It has degree 4, it is nonamenable, and every tree edge
lies on a 4-cycle, and every rung lies on three of them. The root is `o=(r,0)`,
and `B_R` is the induced graph ball.

Removing a rung pair `{(u,0),(u,1)}` disconnects `G`. So every side subtree
hanging off the tree geodesic `r=v_0,...,v_k` is a two-terminal gadget, and it
matters only through whether it joins its two terminals. With `h(d)=0` for
`d>=R` and, for `d<=R-1`,

```text
g(d) = 1-(1-z)(1-h(d+1))^2,     h(d) = z^2 g(d),
```

the geodesic strip becomes a ladder with effective rungs
`r_j = 1-(1-z)(1-h(j+1))^(s_j)`, where `s_j` is the number of side children.
The ladder is then processed by a three-state transfer matrix:

- S1: both terminals are joined to `o`;
- S2: only the top terminal is joined to `o`;
- S3: only the bottom terminal is joined to `o`;
- the state "neither" is absorbing and has value zero, because `o` lies behind
  the pair.

Every step is a polynomial identity in `z`, so it holds for complex `z`. It
was checked two ways:

- exhaustively (all `2^16` edge sets of `B_2`) at `z=0.37+0.21i`, with error at
  most `4e-13` (`check_bruteforce.py`);
- by Monte Carlo on `B_5` at `p=0.55`, with all |z-scores| below 1.8
  (`check_montecarlo.py`).

The walk law of (tree distance, level) is an exact finite dynamic program.

## 2. Thresholds, and the flat-rate point equals the l2 point

For `R = infinity`, the interior rung is `r(p) = 1-(1-p)(1-p^2 g*)`, where
`g*` is the increasing limit of `g_R`. Let `mu(p)` be the Perron root of the
transfer matrix `T(r)`. The matrix `T^2` is positive, so
`tau_p(o,(v_k,i)) = c_i(p) mu(p)^k (1+o(1))` with `c_i > 0`. The sphere at
tree depth `k` has `3*2^(k-1)` tree vertices. Hence:

- `E|C(o)| < infinity` iff `2 mu < 1`, so `p_c = p_T = 0.3805530886`;
- `sum_x tau^2 < infinity` iff `2 mu^2 < 1`, so the l2 point is
  `p_2 = 0.5262004719`;
- `rho = (2 sqrt 2 + 1)/4 = 0.9571067812`.

These values are computed by `thresholds.py`.

**Flat-rate point.** Let `p_* = sup{p : lambda(p) = rho}`. Then `p_* = p_2`
on this graph, by the following argument.

1. The tree distance `D_n` of the walk is a reflected birth-death chain. Away
   from 0 its steps are `+1` with probability 1/2, `-1` with probability 1/4
   and `0` with probability 1/4.
2. Up to bounded factors, `a_n ≍ E[mu^(D_n)]`.
3. With `phi(w) = w/2 + 1/(4w) + 1/4`, the exponential rate of `E w^(D_n)` is
   `max(rho, phi(w))`. This is the usual tilt-or-reflect dichotomy, as for
   `E z^|X_n|` on `T_d`.
4. `phi` has its minimum `rho` at `w = 1/sqrt 2`.
5. So `lambda(p) = rho` iff `mu(p) <= 1/sqrt 2` iff `p <= p_2`, using that
   `mu` is increasing in `p`.

The coincidence is structural. The forward/backward ratio of the distance
chain, `(1/2)/(1/4)`, equals the branching number 2. So the reflection point of
the chain is `w = 2^(-1/2)`, which is also the l2 point of a radial `mu^k`
profile. The same argument gives `p_* = p_2` on `T_d`, with value
`1/sqrt(d-1)`.

`pinch.py` Part 2 gives the finite-`n` rate `(a_(2n)/a_n)^(1/n)` at `n = 400`:

| `p` | 0.30 | `p_c` | 0.45 | 0.50 | `p_2` | 0.55 | 0.60 | 0.70 |
|---|---|---|---|---|---|---|---|---|
| rate | 0.95474 | 0.95479 | 0.95499 | 0.95556 | 0.95631 | 0.95752 | 0.96216 | 0.97639 |

The baseline is `rho * 2^(-3/(2n)) = 0.95462`, which accounts for the
`n^(-3/2)` correction. The rate leaves the baseline around `p_2`, smoothed at
finite `n`.

## 3. Zero data

**(Z) and (G) on discs about `p_c`** (`zeros.py circles`). We take
`n in {20, 50, 100, 200, 400}` and `R in {n, n+1, 2n, 8n}`, and discs
`|z - p_c| < 0.08` and `|z - p_c| < 0.13`. The larger disc reaches `0.5106`,
which is below `p_2`.

- The argument principle counts **0 zeros** in every case, with the maximal
  argument step at most `0.003`.
- `max |a|^(1/n)` on the circle stays below `0.951 < 1`, so (G) holds with
  `M = 0`.
- The values do not depend on `R` to the printed digits.

**Where the zeros are** (`zeros.py map 200 400`; `pinch.py` Part 1).

- For `n = 200` and `R = 400`, the zeros found in `[0,1] x [-0.6,0.6]` form
  two conjugate arcs:
  - one arc near `Im z ≈ ±0.5`, over `Re z` in `[0.15, 0.40]`;
  - one arc descending towards the real axis over `Re z` in `[0.50, 0.60]`.
- The lowest zero of `a_(n,2n)` in the strip `0.40 <= Re z <= 0.70` lies in the
  box `Re z` in `[0.55, 0.56]`, with `Im z`:

| `n` | 100 | 200 | 400 | 800 |
|---|---|---|---|---|
| lowest `Im z` | none below 0.20 | 0.17 | 0.12 | 0.08 |

The height drops by about `sqrt 2` each time `n` doubles, so it scales like
`n^(-1/2)`. The zeros pinch the real axis at `p_2`, not at `p_c`.

**(G) uniformly in `R`** (`pinch.py` Part 3). For fixed `n`, `a_(n,R)(z)`
depends on `R` only through the gadget values `h(d)`, `d <= n+1`. Each of
these is `z^2` times an `(R-d)`-fold iterate of `g -> 1-(1-z)(1-z^2 g)^2`
started at 0. So `sup_R |a_(n,R)(z)|` is finite wherever that orbit stays
bounded. Where the orbit escapes, the effective rungs diverge as `R` grows, and
(G) fails unless there is accidental cancellation. In practice, then, `U` must
lie in the bounded-orbit set `K`. On the real axis the map contracts
on `[0,1]`: its derivative is at most `2(1-z)z^2 <= 8/27`. The sampled
boundary of `K` is at `|Im z| >= 0.43` for `Re z` in `[-0.2, 1.2]`
(`0.57` at `Re z = 0.4`). So `K` is not the binding constraint here.

## 4. Why the zeros must pinch at p_*, and the T_3 correction

**Pinch lemma.** Let `N` be an open disc about a real point `p_0` in `(0,1)`.
Suppose that for all `n >= n_0` and `R >= n`, the function `a_(n,R)` is
zero-free on `N` and satisfies `|a_(n,R)| <= e^(Mn)` there. Then `log lambda`
is real-analytic on `N ∩ R`.

*Proof sketch.* This is the Vitali argument of
`fpbs-zero-free-connectivity-gives-flat-rate`, run on a disc.

1. Fix `n`. As `R -> infinity`, `a_(n,R)(p)` increases to `a_n(p)` on the real
   segment, and the family is uniformly bounded. By Vitali, `a_(n,R)`
   converges on `N` to an analytic `a_n(z)`.
2. By Hurwitz, `a_n(z)` is zero-free, because `a_n(p) > 0`.
3. So `f_n = (1/n) Log a_n` is analytic on `N`, real on the real axis, and
   `Re f_n <= M`.
4. We have `a_n(p) >= p P^n(o,x)` for a suitable `x` at distance at most 1.
   Hence `f_n(p_0) >= log rho - o(1)`.
5. Harnack, applied to `M - Re f_n`, together with Borel–Carathéodory makes
   `{f_n}` normal.
6. On the real axis, `f_n -> log lambda` by Fekete, since `a_n` is
   supermultiplicative. So every subsequential limit is analytic and equals
   `log lambda` on `N ∩ R`. QED.

**Applying it at `p_*`.** Let `p_* = sup{p : lambda(p) = rho}`.

- We have `lambda >= rho`, by step 4 of the proof above.
- `lambda` is nondecreasing, because `tau_p` is.
- `lambda(1) = 1 > rho`.

So `lambda = rho` on `(0, p_*)` and `lambda > rho` on `(p_*, 1]`. Then `lambda`
is not real-analytic at `p_*`. It follows that **every disc about `p_*` fails
(Z) or (G) for infinitely many `n`**.

The same reasoning with the identity theorem gives the following. In (ZG), the
real interval `I_+` must lie in `(p_c, p_*)`. The domain `U` may pass around
`p_*` in the complex plane, but it can never carry the conclusion
`lambda = rho` beyond `p_*`.

**T_3 correction** (`t3_disc.py`). The node's evidence reads: "no zero of
`a_n` in `|z-1/2| < 0.25` for `n <= 200`". That disc contains
`p_*(T_3) = p_2(T_3) = 1/sqrt 2 = 0.7071`, so the pinch lemma says the reading
must eventually fail. The exact counts inside `|z-1/2| < 0.25` are:

| `n` | 100–800 | 1600 | 3200 |
|---|---|---|---|
| zeros | 0 | 2 | 4 |

The zeros come in conjugate pairs and their number grows. The disc
`|z-1/2| < 0.18` stays zero-free for all `n` tested; it avoids `1/sqrt 2`.
So the `n <= 200` reading was a finite-size transient, and it is not evidence
for (Z) on that disc. The live worker `swarm-0917-w8-w8-bs-last1` reached the
same conclusion independently, on the bus, from its weakened ZG.

## 5. What this changes

1. **(ZG) survives the first killing test.** It holds on a cycle-rich Cayley
   graph: exact, uniform in `R`, with `M = 0`, on `|z - p_c| < 0.13`.
2. **The natural zero-free region is cut off at the l2 point, not at `p_c`.**
   On both computable families, `T_d` and `T_3 box K_2`, the zero set pinches
   the real axis exactly at `p_* = p_2`, with height about `n^(-1/2)`.
   Criticality `p_c` is invisible to the zeros.
3. **(ZG) therefore carries no information beyond the flat-rate point.** It
   gives `lambda = rho` only on `(p_c, p_*)`. Its real content is a flat rate
   past `p_c`, that is `p_c < p_*`. This is strictly stronger than the
   right-continuity target (IS) of `fpbs-integrated-sensitivity-universal`.

   One inequality is established: `p_2 <= p_*`, because an `l^2` two-point
   function gives `a_n <= rho^n ||tau||_2`
   (`fpbs-lq-two-point-bounds-walk-rate`, with `q = 2`). In every computed
   example the two points are equal.

   If `p_* = p_2` holds in general (see `fpbs-flat-rate-point-equals-l2-point`),
   then the flat-rate conclusion of the (ZG) route is equivalent to
   `p_c < p_2`. In the notation of the thinning power-monotonicity lemma
   posted live by `swarm-0917-w8-w8-bs-pull`, which has not landed yet, that
   is `q_0 < 2`. The (ZG) route would then be the l2 route in analytic dress.

   The right-continuity routes, lq with `q > 2` and sphere rate, ask for less,
   and they are not collapsed.
