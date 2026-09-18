# The l^q two-point hole is an infinite-cluster statement

swarm-0917-w9-w9-bs-pull, 2026-09-18. Target: `fpbs-two-point-lq-threshold-gap-universal` ([Q]).

## 0. Setting and notation

`G` is a connected, locally finite, transitive, nonamenable graph with root `o`
(in the applications a Cayley graph of a nonamenable group). `P_p` is Bernoulli
bond percolation, `K(o)` the open cluster of `o`, `theta(p) = P_p(|K(o)| = infinity)`.

```text
tau_p(o,x)      = P_p(o <-> x)
tau^fin_p(o,x)  = P_p(o <-> x, |K(o)| <  infinity)
tau^inf_p(o,x)  = P_p(o <-> x, |K(o)| =  infinity)      (tau_p = tau^fin_p + tau^inf_p)
Z_q(p)          = sum_x tau_p(o,x)^q
Z^fin_q(p), Z^inf_q(p)  the same sums for tau^fin_p, tau^inf_p
chi^fin(p)      = E_p[|K(o)| ; |K(o)| < infinity] = sum_x tau^fin_p(o,x)
p_q = sup{p : Z_q(p) < infinity},   q_0 = inf{q >= 1 : p_q > p_c}
```

`q_0` is the one-exponent invariant of `fpbs-lq-threshold-power-monotonicity`
(item 4 there: `{q : p_q > p_c} = (q_0, infinity)`).

Imported input (in the graph, ESTABLISHED): `fpbs-supercritical-finite-susceptibility`,
via `fpbs-hermon-hutchcroft-finite-tail-input` (Hermon–Hutchcroft, arXiv:1904.10448v3,
Theorem 1.1): for every fixed `p > p_c`, `chi^fin(p) < infinity`.

Only Tonelli, independence, Hölder and the elementary inequality
`(a+b)^q <= 2^(q-1)(a^q + b^q)` are used besides that input.

## 1. Theorem A: the finite part is in l^1 at every supercritical p

**Theorem A.** For every `p > p_c` and every `q >= 1`:

1. `Z^fin_q(p) <= chi^fin(p) < infinity`.
2. `Z^inf_q(p) <= Z_q(p) <= 2^(q-1) (chi^fin(p) + Z^inf_q(p))`.
3. Hence `Z_q(p) < infinity  <=>  Z^inf_q(p) < infinity`, and
   `p_q = max(p_c, sup{p > p_c : Z^inf_q(p) < infinity})`,
   `q_0 = inf{q : Z^inf_q(p) < infinity for some p > p_c}`.

*Proof.* (1) `0 <= tau^fin <= 1` and `q >= 1` give `(tau^fin)^q <= tau^fin`;
sum over `x` and use `sum_x tau^fin_p(o,x) = E_p[|K(o)|; |K(o)|<infinity]`
(Tonelli), which is finite by the imported input.
(2) The left inequality is `tau^inf <= tau`. For the right one,
`tau^q = (tau^fin + tau^inf)^q <= 2^(q-1)((tau^fin)^q + (tau^inf)^q)` by convexity
of `t -> t^q`; sum and use (1).
(3) is immediate from (1)–(2), since `Z_q` is nondecreasing in `p` and
`p_q >= p_1 = p_c`. QED.

**Reading.** The exponent `q_0`, and hence [Q] (`q_0 <= 2`) and `p_c < p_2`
(`q_0 < 2`), depend on the infinite-cluster profile `tau^inf_p` alone. The
finite clusters contribute an `l^1` function at every supercritical `p`, with
no dependence of the *summability class* on `p`; only the size of the constant
`chi^fin(p)` depends on `p`, and it does not enter the threshold.

## 2. Theorem B: integer moments are intersections of independent infinite clusters

Let `omega_1, ..., omega_k` be independent `P_p` configurations, `K^i(o)` the
cluster of `o` in `omega_i`, and `K^i_inf(o) = K^i(o)` if it is infinite and
the empty set otherwise.

**Theorem B.** For every integer `k >= 1` and every `p`,

```text
Z_k(p)     = E_(p^k) | K^1(o)     ∩ ... ∩ K^k(o)     |,
Z^inf_k(p) = E_(p^k) | K^1_inf(o) ∩ ... ∩ K^k_inf(o) |.
```

*Proof.* `|∩_i K^i_inf(o)| = sum_x prod_i 1{x in K^i(o), |K^i(o)| = infinity}`.
Take expectations, exchange sum and expectation (Tonelli) and factor the
product by independence: each factor has mean `tau^inf_p(o,x)`. The first
identity is the same computation without the infiniteness indicator. QED.

**Corollary B'.** For an integer `k`: `p_c < p_k` iff at some `p > p_c` the
`k` independent `p`-percolation infinite clusters of `o` have finite *expected*
common intersection (Theorems A and B; the finite clusters may be ignored).
On `T_d` the clusters are subtrees, so `∩_i K^i(o)` is the (connected) cluster
of `o` in `omega_1 ∧ ... ∧ omega_k`, which is `p^k`-percolation. This is the
equality case of the thinning inequality in `fpbs-lq-threshold-power-monotonicity`
(`p_k = p_c^(1/k)` on trees). On a graph with cycles the intersection is a
disconnected set, and the whole content of [Q] is how much larger than the
`p^k`-cluster it is.

## 3. Theorem C: one finite exponent anywhere already gives the worst-pair kernel

Let `gr = lim_n |B_n|^(1/n)`. Since `B_(m+n)` is covered by the balls `B_n(y)`,
`y in B_m`, `|B_(m+n)| <= |B_m| |B_n|`, so by Fekete `gr = inf_n |B_n|^(1/n)`
and `|B_n| >= gr^n` for every `n`. Nonamenable transitive graphs have `gr > 1`.
Let `kappa_p(n) = min_(v in B_n) tau_p(o,v)` and `gamma(p) = lim -(1/n) log kappa_p(n)`
as in `fpbs-worst-pair-connectivity-rate-kernel`.

**Theorem C.** Suppose `Z_q(p) < infinity` for some `p in (0,1]` and some `q in [1, infinity)`. Then:

1. `gamma(p) >= (log gr)/q`.
2. `E_p[|K(o) ∩ B_n| ; |K(o)| = infinity] <= |B_n|^(1-1/q) Z^inf_q(p)^(1/q)`, so
   `limsup_n (1/n) log E_p[|K(o) ∩ B_n| ; |K(o)| = infinity] <= (1 - 1/q) log gr`.
3. `P_p` has no unique infinite cluster; if `p > p_c` then `p_c < p <= p_u`.

*Proof.* (1) Fix `c < (log gr)/q`. By Chebyshev,
`#{v : tau_p(o,v) >= e^(-cn)} <= e^(cqn) Z_q(p)`. Since `|B_n| >= gr^n` and
`e^(cq) < gr`, for all large `n` the ball `B_n` contains a `v` with
`tau_p(o,v) < e^(-cn)`, i.e. `kappa_p(n) < e^(-cn)`. So `gamma(p) >= c`; let
`c -> (log gr)/q`.
(2) Hölder on `B_n` with exponents `q/(q-1)` and `q`:
`sum_(v in B_n) tau^inf_p(o,v) <= |B_n|^(1-1/q) (sum_v tau^inf_p(o,v)^q)^(1/q)`; the left side is
`E_p[|K(o) ∩ B_n|; |K(o)| = infinity]` by Tonelli, and `Z^inf_q <= Z_q`.
(3) Uniqueness gives `tau_p(o,v) >= theta(p)^2` for all `v` (Harris-FKG), which
is incompatible with `Z_q(p) < infinity` when `theta(p) > 0`; if `theta(p) = 0` there
is no infinite cluster at all. For `p > p_c`, `theta(p) > 0`, so there are
infinitely many infinite clusters at `p`, and `p_u >= p` by monotonicity of
uniqueness (Häggström–Peres–Schonmann, as used in the route
`fpbs-bs-via-worst-pair-connectivity-rate`; alternatively item 2 of
`fpbs-worst-pair-connectivity-rate-kernel` with (1)). QED.

So `q_0 < infinity` implies the kernel (K) of
`fpbs-worst-pair-connectivity-rate-positive-above-pc-universal` with the explicit
rate `gamma(p) >= log(gr)/q`, and it implies input (a) of that node's (a)/(b)
split with growth exponent at most `(1-1/q) log gr < log gr`.

## 4. The new hole [Q_fin] and where it sits

**[Q_fin]** (`fpbs-two-point-some-lq-above-pc-universal`). On every nonamenable
Cayley graph `q_0 < infinity`: some `p > p_c` and some integer `k` have
`E_(p^k)|K^1_inf(o) ∩ ... ∩ K^k_inf(o)| < infinity`.

Chain of implications (each arrow proved here or in the cited node):

```text
p_c < p_(2->2)  =>  p_c < p_2 (q_0 < 2)  =>  [Q] (q_0 <= 2)  =>  [Q_fin] (q_0 < inf)
        =>  (a) infinite clusters grow below gr      =>  (K) gamma(p) > 0  =>  p_c < p_u
```

The arrow `[Q] => [Q_fin]` is `q = 3`. The arrows out of `[Q_fin]` are Theorem C.
[Q_fin] is the weakest statement of the whole `l^q` family that still closes
the flagship, and it is the natural target for methods that produce *some*
polynomial moment bound on independent-cluster intersections without the sharp
exponent 2. Every obstruction recorded against [Q] that is tied to the exponent
2 (the thinning exponent transfer of `fpbs-lq-threshold-power-monotonicity`
Section 5, which needs `(p')^q > p_c^2`) does not apply to [Q_fin] as stated; the
exponent-free obstructions (the collapse witness of
`fpbs-two-point-state-axioms-admit-collapse`, which lies in no `l^q`) do.

Neither converse is known: [Q_fin] asks for polynomial (in `l^q`) decay of
`tau^inf` somewhere above `p_c`, while (K) only asks for one exponentially rare
pair per ball. Between `p_c < p_u` and [Q_fin] sits the question whether
`tau_p` in `c_0` (Lyons–Schramm, for `p < p_u`) upgrades to `tau_p` in some `l^q`.

## 5. Attempt (not established): Russo–BK openness with the pivotal split

The w5 attempt on [Q] majorised `d Z_q/dp` by a BK convolution containing
`tau * tau`, infinite above `p_c` because `chi_p = infinity`. Theorem A suggests
splitting each pivotal edge `e = {u,v}` for `{o <-> x}` by which side is finite
once `e` is closed:

- **o-side finite.** Conditioning on `K(o) = C` (finite, `v` not in `C`) and
  using that `{v <-> x off C}` depends only on edges off `C`, the contribution is
  at most `c_p tau^fin_p(o,u) tau_p(v,x)`.
- **x-side finite.** Symmetric: at most `c_p tau_p(o,u) tau^fin_p(v,x)`.
- **both sides infinite.** `D_p(o,x) = sum_e P_p(e pivotal, both sides infinite)`:
  two distinct infinite clusters touching along `e`.

For the two finite-side terms, Young's inequality with `tau^fin` in `l^1`
(Theorem A) bounds their contribution to `sum_x q tau^(q-1) d tau/dp` by
`C_p chi^fin(p) Z_q(p)`. So the `chi_p = infinity` obstruction of the w5 attempt
disappears for them.

**Where it dies (two independent points).**

1. **Gronwall through `p_c`.** Openness from `p_c` needs
   `integral_(p_c) chi^fin(s) ds < infinity`. On `T_d` (the calibration), mean-field
   `gamma' = 1` gives `chi^fin(p) ≍ (p - p_c)^(-1)` (recalled, Grimmett,
   *Percolation*, 2nd ed., Section 10.1; not load-bearing). So the integral
   diverges logarithmically and the bound is vacuous, although `Z_q` is finite
   and smooth through `p_c` there for every `q > 1`. Young with the `l^1` norm
   of `tau^fin` loses exactly one factor `chi^fin`. Replacing `l^1` by `l^r`,
   `r > 1`, needs `tau` in `l^s` with `1/r + 1/s = 1 + 1/q` and `s < q`: the
   finiteness of a *lower* moment. That is circular, the same exponent circle
   as the thinning transfer.
2. **The both-infinite term.** `D_p` is supported on configurations with at
   least two infinite clusters. It is the only term that sees the
   nonuniqueness phase. Bounding it needs the joint law of two distinct
   adjacent infinite clusters (the object of the open
   `fpbs-pivotal-budget-universal`), and no finite-cluster input controls it.

Conclusion: after the split, Russo–BK openness for [Q] reduces to (i) an
integrable-in-`p` replacement for `chi^fin` near `p_c`, which fails on trees
for every method that uses only `||tau^fin||_1`, and (ii) a bound on `D_p`.

## 6. What Theorem A kills and what it does not

Theorem A makes [Q] and [Q_fin] statements about `tau^inf` alone. Combine it with
(H2) and (H5) of `fpbs-sharp-dominating-collapse-over-sparse-spines`: those
collapse families have exactly the Bernoulli finite clusters, matching `theta`
and ball laws, but a unique infinite cluster, hence `q_0 = infinity`. The result
is the sharp form of an obstruction already implicit in the graph. **No argument
whose above-`p_c` inputs are finite-cluster observables, `theta` and ball laws
can prove [Q_fin], hence none can prove [Q],** on any graph with invariant
sparse spines. The invariant is `q_0`, computed from `tau^inf`. Every member of
the class dies at the step where it must bound `tau^inf` in some `l^q`, since
that quantity is invisible to its inputs. This is not a new class kill. It is
the sharpest statement of which data [Q] depends on.
