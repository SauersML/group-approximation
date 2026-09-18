# Zero-free connection polynomials and the flat walk rate

Status: one conditional theorem with a complete proof (Section 2), one open
universal hypothesis (Section 3), and a calibration computation (Section 4).
Written for the hole `fpbs-pivotal-budget-universal` by the reframer lane of
wave swarm-0917. Nothing here proves `fpbs-benjamini-schramm-universal`.

## 1. The reframing

The pivotal budget (PB) asks for a real-variable bound on the logarithmic
derivative `p (d/dp) log a_(n,R)(p) = E_p[N_(n,R) | E_(n,R)]` on `[p_c,p_0]`,
uniformly in `n` and `R>=n`. Every attempt recorded on that hole works with
real parameters: triangle charging, bridges, structure, BK bubbles, finite
models, states.

Here the parameter becomes complex. For a finite ball, `a_(n,R)(z)` is a
polynomial in `z`. A bound on the logarithmic derivative on a real segment
follows when `log a_(n,R)` is analytic on a complex neighbourhood with a
real part of order `n`. A zero-free region with a growth bound therefore
controls the budget. It also makes the exponential rate `lambda` analytic,
and that is much stronger. Since `lambda` is constant on `(0,p_c]`, the
identity theorem carries the constant past `p_c`, provided the domain lets
one continue around `p_c` through the complex plane. The singular point
`p_c` never has to be crossed on the real axis.

Notation, as in Section 6 of
`research/artifacts/fpbs/exploration-pivotal-projections.md`. `G` is a
nonamenable locally finite Cayley graph and `X_n` is simple random walk from
`o`, independent of the percolation. `rho=||P||<1` (Kesten).

- `B_R` is the ball of radius `R` about `o`.
- `E_(n,R)` is the event that `o` connects to `X_n` by open edges of `B_R`.
- `a_(n,R)(p)=P_p(E_(n,R))`, `a_n(p)=lim_R a_(n,R)(p)`, and
  `lambda(p)=lim_n a_n(p)^(1/n)`.

The rate `lambda` exists by FKG supermultiplicativity, `lambda>=rho`, and
`lambda(p_c)=rho` by Schramm's lemma; this is the established
`fpbs-integrated-pivotal-rate-identity`. Since `a_n` is nondecreasing in `p`,

    lambda(p) = rho   for every 0 < p <= p_c.                  (1.1)

For each `n` and `R`, `a_(n,R)(z)` is a polynomial in `z`: it is a finite
average over `X_n` of the reliability polynomial of `B_R`.

## 2. Conditional theorem

**Hypothesis (ZG) for G.** There are:

- a simply connected domain `U` in `C`;
- open intervals `I_-` contained in `(0,p_c]` and `I_+` contained in
  `(p_c,1)`, both contained in `U`;
- constants `M` and `n_0`;

such that for all `n>=n_0` and all `R>=n`:

- (Z) `a_(n,R)` has no zero in `U`;
- (G) `|a_(n,R)(z)| <= exp(M n)` for all `z` in `U`.

`U` need not contain `p_c`. It may go around `p_c` through the upper half
plane.

**Theorem 2.1.** If (ZG) holds for `G`, then:

- (a) `lambda(p)=rho` for every `p` in `I_+`;
- (b) every `p` in `I_+` is in the nonuniqueness phase, so `p_c<p_u`;
- (c) for every compact interval `J` in `I_- union I_+` there is `C_J` with
  `E_p[N_(n,R)|E_(n,R)] <= C_J n` for all `p` in `J`, `n>=n_0` and `R>=n`.

**Proof.**

*Step 0: a real lower bound.* For real `w` in `(0,1)` and `R>=n`, the walk
path has length `n` and lies in `B_n`, which is contained in `B_R`. Opening
its edges gives `a_(n,R)(w) >= w^n`.

*Step 1: local bounds uniform in (n,R).* By (Z) and simple connectivity,
`F_(n,R)=log a_(n,R)` has an analytic branch on `U`. Take the branch real at
a fixed point `w_-` of `I_-`. Then:

- `u=Re F_(n,R)/n = n^(-1) log|a_(n,R)|` is harmonic.
- `u <= M` by (G).
- `u(w_-) >= log w_-` by Step 0.

`h=M-u` is a nonnegative harmonic function on the connected domain `U`, so
either `h` vanishes identically or `h>0`. Fix a compact connected set `K` in
`U` containing `w_-`. Harnack's inequality gives

    sup_K h <= C_K h(w_-) <= C_K (M - log w_-),

with `C_K` depending only on `K` and `U`. So `|Re F_(n,R)/n| <= A_K`
uniformly in `n>=n_0` and `R>=n`.

`Im F_(n,R)(w_-)=0`. The Borel–Carathéodory inequality on a finite chain of
discs from `w_-` covering `K`, whose doubles lie in `U`, bounds
`|F_(n,R)/n|` on `K` by a constant `B_K`, again uniformly in `(n,R)`.
Exhausting `U` by such `K` shows that `{F_(n,R)/n}` is locally uniformly
bounded, hence a normal family (Montel).

*Step 2: R to infinity at fixed n.* Increasing events give
`a_(n,R)(p) -> a_n(p) >= p^n > 0` for real `p`. Any locally uniform
subsequential limit of `F_(n,R)/n` as `R -> infinity` is analytic on `U` and
equals `n^(-1) log a_n` on `I_-`. So all such limits agree on `I_-`, and by
the identity theorem they agree on `U`. Hence `F_(n,R)/n` converges locally
uniformly to an analytic `g_n`.

`g_n` is bounded by `B_K` on each `K`. For real `p` in `I_+`,
`Re g_n(p) = n^(-1) log a_n(p)`.

*Step 3: n to infinity.* `{g_n}` is normal. Let `g` be a subsequential
limit. On `I_-`, `g_n(p)=n^(-1) log a_n(p) -> log lambda(p) = log rho` by
(1.1). So `g` is constant on an interval, and by the identity theorem
`g = log rho` on all of `U`. For `p` in `I_+`,

    log lambda(p) = lim_n n^(-1) log a_n(p) = lim Re g_n(p) = Re g(p) = log rho.

This proves (a).

*Step 4: nonuniqueness.* Let `p` be in `I_+`. By (a),
`a_n(p) <= ((1+rho)/2)^n` for large `n`, so `a_n(p) -> 0`. Since `p>p_c`,
`theta(p)>0`. If there were a unique infinite cluster, Harris–FKG would give
`tau_p(x,y) >= theta(p)^2` for all `x,y`, hence `a_n(p) >= theta(p)^2`, which
is a contradiction. By Newman–Schulman, the number of infinite clusters is
infinite. So `p<=p_u`, and (b) follows by taking any `p` in `I_+`. In fact
`p_c < inf I_+ < sup I_+ <= p_u`.

*Step 5: budget.* Let `J` be in `I_+` (or in `I_-`). Choose `r>0` with
`D(p,2r)` contained in `U` for every `p` in `J`, and let `K` be the closure
of the union of these discs. The Cauchy estimate on `D(p,r)` gives
`|F'_(n,R)(p)| <= B_K n / r`. Since `p F'_(n,R)(p) = E_p[N_(n,R)|E_(n,R)]` by
the finite Russo identity (P1), (c) holds with `C_J = B_K / r`. QED.

**What (ZG) buys that (PB) does not.**

- (PB) gives only a Lipschitz rate, `lambda(p) <= rho (p/p_c)^C`.
- (ZG) gives a *flat* rate on `I_+`: the same conclusion the critical l2
  gap gives below `p_(2->2)` (Proposition 6.4 of H18, quoted in Section 6.1
  of the exploration note).
- (ZG) never needs a real-variable bound at `p_c` itself.

Conversely, (c) is a budget only on intervals that avoid `p_c`. So (ZG) is
not a route to (PB) on `[p_c,p_0]`, and (PB) is not a route to (ZG). Both
routes sit separately under `fpbs-benjamini-schramm-universal`.

**Necessary consequences of (ZG), each falsifiable on its own.**

- (N1) Flatness: `lambda = rho` on an interval to the right of `p_c`. Under
  `p_c=p_u`, `lambda=1` there, so (ZG) fails on every graph with coinciding
  thresholds. On the tree, `lambda` is flat exactly up to
  `p_(2->2)=1/sqrt(d-1)`.
- (N2) Fixed-n analytic continuation: for every `n`, the true `a_n` on `I_+`
  is the analytic continuation along `U` of `a_n` restricted to `I_-`.
  This is a statement about one two-point average and no limit in `n`. A
  second-order singularity of `tau_p(o,x)` at `p_c`, for one fixed `x`, would
  kill (ZG) on every domain `U`. No such singularity is proved on any graph.
  On trees `tau_p(o,x)=p^|x|` is entire.
- (N3) Uniform growth (G) as `R -> infinity`. This is the gate (Section 4).
  Many nearly disjoint long routes make complex reliability polynomials
  large. `G` has exponentially many self-avoiding paths of length `L` with
  expected open count `(p mu)^L`, where `mu` is the connective constant, and
  on a graph with cycles `p_c > 1/mu` is expected. So (G) at the real point
  `p_c` needs cancellation among routes, not a crude path count.

## 3. The open universal hypothesis

`fpbs-connectivity-polynomials-zero-free-around-criticality`: every
nonamenable Cayley graph satisfies (ZG) for some `U`, `I_-`, `I_+`, `M`,
`n_0`. With Theorem 2.1, it gives `fpbs-benjamini-schramm-universal`.

Where it is known:

- *Trees `T_d`, d>=3.* `a_(n,R)(z)=E z^|X_n|` for every `R>=n`, a
  polynomial with nonnegative coefficients summing to one. So
  `|a_(n,R)(z)| <= 1` on `|z|<=1`, and (G) holds with `M=0`. (Z) on a disc
  about `p_c=1/(d-1)` is supported numerically in Section 4, not proved.
- *Cactus Cayley graphs, such as free products of finite cyclic groups
  whose Cayley graph is a cactus.* `tau_p(o,x)` is the product of the block
  reliabilities along the block path, independent of `R>=|x|`. (G) holds on
  `|z|<=1`, and (Z) reduces to zeros of finitely many block polynomials and
  of the walk average. It is not checked here.

No graph with multiscale cycle overlap has been tested. Under `p_c=p_u`, (ZG)
must fail by Theorem 2.1(b).

## 4. Calibration computation

Script: `experiments/fpbs-zero-free-2026-09-17/tree_walk_connectivity_zeros.py`
(standard library only, about a minute).

*T_3, simple random walk.* Here `p_c=1/2` and `p_(2->2)=0.7071`. The script
counts zeros of `a_n(z)=E z^|X_n|` by the argument principle:

| n | zeros in `|z-0.5|<0.15` | zeros in `|z-0.5|<0.25` | zeros in `|z-0.7071|<0.05` | sup of `|a_n|` on `|z-0.5|=0.25` |
|---|---|---|---|---|
| 20 | 0 | 0 | 0 | 1.68e-1 |
| 40 | 0 | 0 | 0 | 4.60e-2 |
| 80 | 0 | 0 | 0 | 4.05e-3 |
| 120 | 0 | 0 | 0 | 3.82e-4 |
| 160 | 0 | 0 | 0 | 3.71e-5 |
| 200 | 0 | 0 | 0 | 3.66e-6 |

- (Z) holds numerically on a disc containing `p_c`, for `n<=200`.
- The boundary supremum decays at about `rho^n`, with `rho=2 sqrt(2)/3=0.943`.
  This is consistent with the flat rate.
- No zero approached `p_(2->2)` within `0.05` for `n<=200`. Any pinching
  there is slower than this window detects, and no claim is made about it.

*Parallel-routes toy.* `tau(z)=1-(1-z^L)^m` with `m=2^L`: `m` disjoint
routes of length `L` at the path-count threshold `1/2`. On the circle
`|z-0.5|=0.1`:

| L | sup of `|tau|` on the circle | zeros inside |
|---|---|---|
| 4 | 0.894 | 0 |
| 8 | 1.40 | 0 |
| 12 | 4.56 | 0 |
| 16 | 106 | 2 |

The real values stay in `[0,1]`, yet the modulus off the axis grows without
bound, and zeros enter the disc once the routes are long. This is the
mechanism behind (N3). A Cayley graph with exponentially many overlapping
detours must supply cancellation that this toy lacks, or (ZG) fails there.

## 5. Disposition

- Established (conditional): Theorem 2.1, recorded as
  `fpbs-zero-free-connectivity-gives-flat-rate`.
- Open: `fpbs-connectivity-polynomials-zero-free-around-criticality`, which
  splits into (Z) and (G) and carries the necessary consequences (N1)–(N3).
- Route: `fpbs-zero-free-connectivity-route`, to
  `fpbs-benjamini-schramm-universal`.
- The first test that could kill the route: compute `a_(n,R)(z)` exactly for
  small `n` and growing `R` on a small nonamenable Cayley graph with
  overlapping cycles, for example `C_2 * C_2 * C_2 x C_2`, and watch
  `sup |a_(n,R)|` on a fixed circle about `p_c` as `R` grows. Bounded growth
  supports (G); growth exponential in `R` kills (ZG) for that `U`.
