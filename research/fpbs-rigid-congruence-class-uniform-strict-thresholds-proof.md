---
rg: 2
id: fpbs-rigid-congruence-class-uniform-strict-thresholds-proof
kind: route
title: Covering monotonicity of theta and fibre sums, a chord-weighted Busemann-Schur certificate on F_2 x Z^3, and a no-wrap star-stage Galton-Watson certificate on F_2 x Z/N
target: fpbs-rigid-congruence-class-uniform-strict-thresholds
requires: []
artifacts:
  - experiments/fpbs-congruence-sandwich-2026-09-17/schur3.py
  - experiments/fpbs-congruence-sandwich-2026-09-17/exactschur.py
  - experiments/fpbs-congruence-sandwich-2026-09-17/famschur.py
  - experiments/fpbs-congruence-sandwich-2026-09-17/starzw.c
  - experiments/fpbs-congruence-sandwich-2026-09-17/certgw.py
  - experiments/fpbs-congruence-sandwich-2026-09-17/mcgen.c
  - experiments/fpbs-congruence-sandwich-2026-09-17/outputs.txt
---

**Setting.**
* For an abelian group `B` with elements `y, z, w`, put `Gamma_B = F_2 x B` and
  `S_B = {(a,0),(a,y),(a,z),(b,0),(b,y),(b,w),(1,y)}^{±1}`, and let `G_B` be the
  Cayley graph. Vertices are `(v,h)` with `v in F_2`, `h in B`.
* Edges:
  * vertical edges `(v,h) ~ (v,h+y)`;
  * ladder edges `(v,h) ~ (vl, h+d)`, for `l = a` with `d in D_a = {0,y,z}` and
    for `l = b` with `d in D_b = {0,y,w}`. The inverse letters carry `-D_l`.
* We always assume the seven elements of `S_B` in the positive list are distinct,
  so `G_B` is simple and 14-regular.
* `tau^B_p(x,x') = P_p(x <-> x')` and `T^B_p` is the operator with kernel `tau^B_p`.
* The fibre sum is `fbar^B(v) = sum_{h in B} tau^B_p(o,(v,h))`.

Three instances matter:
* the **cover** `B = Z^3`, with `(y,z,w) = (e_1,e_2,e_3)`;
* the **member** `B = A`, as in the claim;
* the **quotient** `B = Q in {Z, Z/N}`, with `(y,z,w) = (1,z0,w0)`.

The certified patterns satisfy `3 <= z0 < w0 <= 6`. So `0,1,z0,w0` are distinct in
`Z/N` for `N >= 14`, and the member's generators are distinct, because they have
distinct images under `chi`.

## Step 1. From the two bounds to strict thresholds

Suppose `theta(p) > 0` and `||T_p||_{2->2} < infinity` on a transitive graph.
If there were a unique infinite cluster, Harris-FKG would give
`tau_p(o,x) >= P(o <-> infinity, x <-> infinity) >= theta(p)^2` for all `x`. Then
`sum_x tau_p(o,x)^2 = ||T_p δ_o||^2 <= ||T_p||^2` would be infinite. So there is
nonuniqueness at `p`.

Uniqueness is monotone in `p` (Häggström-Peres 1999; Schonmann 1999). Also
`||T_p||` is nondecreasing in `p`. Hence, if `theta(p1) > 0` and
`||T_(p2)|| < infinity` with `p1 < p2`, then `p_c <= p1 < p2 <= p_{2->2} <= p_u`.

## Step 2. Covering lemmas

Let `phi : B' -> B` be a homomorphism sending `(y',z',w')` to `(y,z,w)`, where both
generating lists consist of distinct elements. Put `Phi = id x phi`. Then `Phi`
maps the star of `x'` bijectively onto the star of `Phi(x')`, so it is a covering
map `G_{B'} -> G_B` that preserves the `F_2` coordinate. Both maps in the tower
`Z^3 -> A -> Q` are of this kind.

**Lemma 2.1 (lifting the exploration).** For every `p` there is a coupling of
Bernoulli(`p`) configurations `omega` on `G_B` and `omega'` on `G_{B'}` such that
`Phi` maps a subset of `C'(o')` bijectively onto `C(o)`. Consequently:
* `theta_{B'}(p) >= theta_B(p)`;
* for every `v in F_2`, `E|C'(o') ∩ ({v} x B')| >= E|C(o) ∩ ({v} x B)|`, that is,
  `fbar^{B'}(v) >= fbar^B(v)`.

*Proof.*
1. Explore `C(o)` with a fixed deterministic rule that grows a spanning tree `T`.
   At each step it takes a tree vertex `x` and a generator `s` with `xs` not in
   `T`, and reveals the edge `{x, xs}`. Each edge is revealed at most once.
2. Run a shadow explorer on `G_{B'}` that maintains a tree `T'` and a bijection
   `T' -> T` given by `Phi`. When the base explorer reveals `{x, xs}`, the shadow
   reveals `{x', x's'}`, where `x'` is the lift of `x` in `T'` and `s'` is the
   generator over `s`. It copies the coin, and it adds `x's'` to `T'` exactly when
   `xs` is added to `T`.
3. Distinct base vertices have distinct lifts, so `T'` is an embedded tree. The
   shadow edges have pairwise distinct images, so they are pairwise distinct. The
   copied coins are therefore i.i.d. Bernoulli(`p`) on distinct edges of `G_{B'}`.
   Fill every other edge of `G_{B'}` with an independent coin. This gives
   `omega'`, a Bernoulli(`p`) configuration.
4. `T'` is open in `omega'`, contains `o'`, and maps bijectively onto `C(o)` while
   preserving the `F_2` coordinate. Both consequences follow. ∎

The inequality `p_c(G_{B'}) <= p_c(G_B)` is Benjamini-Schramm (1996, Theorem 1).
The fibre version is what we need on the `l^2` side.

**Lemma 2.2 (fibre Young inequality).** For every abelian `B`,
`||T^B_p||_{l^2(F_2 x B)} <= ||lambda_{F_2}(fbar^B)||`.

*Proof.* Write `f = tau^B_p(o,·) >= 0` and take `u in l^2(F_2 x B)`. Put
`U(v) = ||u(v,·)||_{l^2(B)}`. Then `T u = f * u`, and for each `v`

```text
||(f*u)(v,·)||_2  <=  sum_{v'} || f(v',·) * u(v'^{-1} v, ·) ||_2
                  <=  sum_{v'} ||f(v',·)||_1 U(v'^{-1} v)  =  (fbar * U)(v)
```

by Minkowski's inequality and Young's inequality `l^1 * l^2 -> l^2` on `B`. So
`||T u|| <= ||lambda(fbar) U|| <= ||lambda(fbar)|| ||u||`. ∎

**Corollary 2.3.** For every member `A`,
`||T^A_p|| <= ||lambda_{F_2}(fbar^{Z^3})||` and `p_c(G_A) <= p_c(G_Q)`.

## Step 3. `||lambda_{F_2}(fbar^{Z^3}_p)|| < infinity` at `p = 93/1000`

**Schur test with Busemann weights.**
* `fbar(v) = fbar(v^{-1})`, because `tau` is symmetric and `(v,h)^{-1} = (v^{-1},-h)`.
  So `K(x,x') = fbar(x^{-1}x')` is a symmetric nonnegative kernel on `F_2`.
* Fix an end `xi` of the 4-regular tree. Let `beta_xi` be its Busemann function with
  `beta_xi(e) = 0`, and put `h_xi = 3^{-beta_xi/2}`.
* For every `x`, `sum_{x'} K(x,x') h_xi(x') / h_xi(x) = sum_g fbar(g) 3^{-beta_{x^{-1}xi}(g)/2}`.
* So `||lambda(fbar)|| <= M := sup_xi sum_g fbar(g) 3^{-beta_xi(g)/2}` by the Schur
  test.

**Chord-weighted path majorant.**
* For each configuration with `o <-> x`, let `gamma(omega)` be the first shortest
  open path from `o` to `x` in a fixed ordering. A *chord* of a self-avoiding path
  `gamma = (gamma_0, ..., gamma_n)` is an edge `{gamma_i, gamma_t}` with `t >= i+2`.
* If `gamma(omega) = gamma` then every chord is closed, since otherwise the path
  could be shortened. Chords are distinct from path edges and from each other.
* Hence `tau(o,x) <= sum_gamma p^n (1-p)^{c(gamma)}`, over self-avoiding paths from
  `o` to `x`.
* Keep only the chords with `t - L - 1 <= i <= t - 2` (memory `L`), and keep only
  the constraint `gamma_t notin {gamma_{t-L-1}, ..., gamma_{t-1}}`. This enlarges
  the sum to `sum over L-local walks of prod_t p (1-p)^{c_t}`, where `c_t` is the
  number of those `i` with `gamma_i ~ gamma_t`.
* Both constraints depend only on the last `L` generators, the *window*, by left
  invariance.

**Transfer operator.**
* A state is `s = (sigma, u)`: a window `sigma` (of length at most `L`) and a letter
  `u in {a, a^-1, b, b^-1}`. The letter `u` records the unique letter at the current
  vertex that lowers `beta_xi`.
* A step by generator `g = (l, d)` from state `s` is allowed if the new vertex is not
  in the window. Its weight is `p(1-p)^c`, where `c` is its chord count, multiplied
  by a factor that depends on `l`:
  * `l = 1` (vertical): factor `1`, and the new letter is `u`;
  * `l = u` (an up step): factor `sqrt 3`, and the new letter is any `u' != u^{-1}`,
    as determined by `xi`;
  * `l != 1, u` (a down step): factor `1/sqrt 3`, and the new letter is `l^{-1}`.
* Define
  `(Tv)(s) = sum_vertical,down wt * v(s') + sum_up wt * sqrt3 * max_{u' != u^{-1}} v(sigma', u')`.
* By induction on `n`, for every `xi`, the weighted sum over `L`-local walks of
  length `n` starting in state `(empty, u_xi(e))` is at most `(T^n 1)(s_0)`. The
  `max` dominates whichever `u'` the end `xi` selects.
* If `Tv <= C v` with `C < 1` and `0 < v_min <= v <= v_max`, then
  `T^n 1 <= C^n v_max / v_min`. So `M <= v_max / (v_min (1 - C))`, uniformly in `xi`.

**Certificate (`exactschur.py`, `mode tri`, `L = 4`, `p = 93/1000`).**
1. *Geometry.* `schur3.build_geometry` enumerates windows exactly. The `Z^3`
   coordinate is encoded as the integer `h_1 + 1000 h_2 + 100000 h_3`. Every
   comparison in the program involves at most `L + 1 = 5` steps, so
   `|h_i| <= 5` and the encoding is injective on the relevant range. There are
   `32569` windows, `417198` allowed transitions, and at most `4` chords per
   transition.
2. *Vector.* A float power iteration gives `v`. It is converted to positive
   integers `V = ceil(2^40 v) + 1`.
3. *Exact check.* Every transition weight is an integer:
   `a(b-a)^c b^{cmax-c}` over the common denominator `b^{cmax+1}`, with
   `p = a/b`. `sqrt 3` is replaced by the upper bound `SP/10^16` on up steps, and
   `1/sqrt 3` by the upper bound `10^16/SM` on down steps, where
   `SM = 17320508075688772 < 10^16 sqrt 3 < SP = SM + 1`. The script checks
   `Tv <= (Cn/Cd) V` entrywise in Python integers.
4. *Result.* The exact maximum of `(TV)_s / V_s` is `0.99987945764...`. The check
   against `C = 9999/10000` returns `True` (see `outputs.txt`). This gives
   `M < infinity` at `p = 93/1000`.
5. *Memory 3.* The same program with `L = 3` certifies `C <= 998/1000` at
   `p = 37/400`: the exact max is `0.997309`.

With Corollary 2.3, `||T^A_{93/1000}|| < infinity` for every member `A`.

## Step 4. `theta > 0` on `G_Q` for the certified patterns

**The star-stage process on `F_2 x Z`.** This is the construction used for `S_rig`,
with `D_a = {0,1,z0}` and `D_b = {0,1,w0}`. Parameters: `W = 6`, `K = 3`, `A = 4`,
cutoff `10^-6`.
* An individual is a fibre `v = v's` with a nonempty height set `G`,
  `|G| <= K`, `max G - min G < W`, entered by the letter `s`. Its type is
  `(s, G - min G)`, giving 64 types.
* Its stage processes a FIFO queue, starting from the vertices of `G`, with
  `min G = 0`.
* Processing a fibre vertex `h`:
  * it reveals the vertical edges to `h ± 1` whose target lies in the window
    `[-A, W-1+A] = [-4, 9]` and is not yet in `P`;
  * for each child letter `t != s^{-1}` and each `d in D_t`, it reveals the ladder
    edge to `(vt, h+d)`, unless `h+d` is already in `C_t`.
* Processing a child vertex `(vt,h')` reveals its back edges to `(v, h'-d)` whose
  target is in the window and not in `P`.
* The stage stops when the queue is empty or when `p^i (1-p)^j < 10^-6`.
* The offspring are `(vt, cap(C_t))`. The cap keeps the heights `< min C_t + W`,
  then the `K` smallest of them.

The standard facts transfer unchanged:
* no edge is revealed twice within a stage;
* stages own disjoint edge sets, namely the vertical edges of their fibre and the
  ladder edges to their children, because the individuals form a subtree of the
  Cayley tree of `F_2`;
* the stopping rule is a stopping time;
* the law depends only on the type.

So this is a 64-type Galton-Watson process with bounded offspring, and
`theta(p) >= p P(survival)`.

**No wrap-around.** Put `m = max(z0,w0)`. Every height a stage touches is one of:
* a fibre height in `[-4, 9]` (the vertices in `P` and the targets of vertical and
  back edges);
* a child height `h + d` with `h in [-4,9]` and `|d| <= m`, so in `[-4-m, 9+m]`.

Both ranges have at most `N0 = 14 + 2m` integers. Now let `Q = Z/N` with
`N >= N0`. Define the stage of an individual `(v, G)`, with a chosen integer lift of
`min G`, as the image of the integer stage under `h -> min G + h mod N`.
* Reduction mod `N` is injective on each of the two ranges. So every membership
  test (`in P`, `in C_t`) has the same answer.
* Distinct revealed integer edges map to distinct edges of `G_{Z/N}`. A vertical or
  back edge is determined by its fibre endpoint and generator. A ladder edge is
  determined by its parent endpoint and generator.
* The caps and child types, computed from integer representatives in
  `[-4-m, 9+m]`, are the same.

So the branch counts `star` records, and hence the mean matrix, are literally the
same on `F_2 x Z/N` as on `F_2 x Z`.

**Certificates (`starzw.c` + `certgw.py`, exact rationals).**
* `starzw.c` is the stage enumerator with the offsets `z0, w0` taken from the
  command line. For `(3,4)` it reproduces the output of the `S_rig` enumerator
  byte for byte: sha256 `b0a83e63...` at `91/1000`.
* The communicating class of `(a,{0})` is all 64 types in every run.
* A rounded-up rational Perron vector gives these exact Collatz-Wielandt minima:

| pattern | `p1` | exact `min (Mv)_k / v_k` |
|---|---|---|
| `(3,4)` | `91/1000` | `1.01605` |
| `(3,5)` | `91/1000` | `1.00856` |
| `(4,5)` | `91/1000` | `1.00642` |
| `(3,6)` | `92/1000` | `1.00117` |
| `(4,6)` | `925/10000` | `1.00577` |

* Each is `> 1`, so `rho(M) > 1`. The process is irreducible with bounded offspring,
  so it survives with positive probability (Harris; Athreya-Ney V; pass to a cyclic
  class of `M^d` in the periodic case).
* Hence `theta_Q(p1) > 0` and `p_c(G_Q) <= p1`.

## Step 5. Assembly

Let `A` be a member with character `chi`.
* `A` is generated by `y,z,w`, so `Z^3 -> A`, `e_i -> (y,z,w)`, is a surjective
  homomorphism.
* `chi` sends `(y,z,w)` to `(1,z0,w0)`.
* All three generating lists consist of distinct elements. So Step 2 applies to both
  maps.
* By Corollary 2.3 and Step 4, `p_c(G_A) <= p_c(G_Q) <= p1`.
* By Corollary 2.3 and Step 3, `||T^A_{93/1000}|| < infinity`.
* Since `p1 <= 925/10000 < 93/1000`, Step 1 gives
  `p_c(G_A) <= p1 < 93/1000 <= p_{2->2}(G_A) <= p_u(G_A)`. ∎

## Step 6. Rigidity of the reduced sets

This step only places the class inside the root's rigid regime. Take `N >= 14` and
a 3-subset of `Z/N` with diameter at most 6. Its three cyclic gaps sum to `N`, and
two of them sum to at most 6. So exactly one gap is larger than 6, and the
translation class of the subset is the ordered pair of the other two gaps.
* `D_a = {0,1,z0}` gives `(1, z0-1)` and `-D_a` gives `(z0-1, 1)`.
* `D_b` gives `(1, w0-1)` and `-D_b` gives `(w0-1, 1)`.

For `3 <= z0 < w0` these four pairs are distinct. A translation over `Z` between
two of the integer sets `D_a, -D_a, D_b, -D_b` of a member of `F_2 x Z` would
reduce to one mod `N`. So the integer sets are pairwise inequivalent.

## What is not proved here

* The generic cover `F_2 x Z^5` numbers (`C = 1.0026` at `0.090` for `L = 3`,
  `C = 1.0072` at `0.0905` for `L = 4`) are float runs of `famschur.py gen`. They
  show only that this certificate does not close there.
* The Monte Carlo numbers from `mcgen.c` are heuristic.
* The failing patterns `(5,6), (3,7), (4,7)` at `925/10000` fail this particular
  Galton-Watson certificate. Nothing is claimed about their thresholds.

## Reproduction

In `experiments/fpbs-congruence-sandwich-2026-09-17/`:

```text
cc -O2 -o starzw starzw.c
./starzw 91 1000 6 3 4 1e-6 3 5 > st.txt && python3 certgw.py st.txt 91/1000 1/1
python3 exactschur.py 4 tri 93 1000 9999 10000     # a few minutes
python3 exactschur.py 3 tri 37 400 998 1000
python3 famschur.py 4 gen 0.0905                   # generic cover, float
cc -O2 -o mcgen mcgen.c && ./mcgen 0.080 1500 20000 1 1
```
