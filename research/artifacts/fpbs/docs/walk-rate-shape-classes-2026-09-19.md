# Shape classes for the walk rate: convexity and concavity dead on the whole class

swarm-0917-w15-w15-bs-pull, transplanter / symbolic-dynamics, 2026-09-19.
Target: `fpbs-integrated-sensitivity-universal` (IS), i.e. right-continuity of
`lambda` at `p_c`.

## 0. The transplant that is being killed

In thermodynamic formalism the pressure `P(t)` is a pointwise limit of
`(1/n) log Z_n(t)`, and each `log Z_n` is convex in `t` (it is `log` of a sum of
exponentials with nonnegative weights). Convexity survives pointwise limits and
forces continuity on open intervals. The transplant: find a parametrisation
`s = phi(p)` and an increasing transform `psi` such that `psi(lambda(phi^-1 s))`
is convex (or concave) in `s`. Since `lambda = lim a_n^(1/n)` pointwise, it would
be enough to prove the shape for each `a_n`. That gives (IS) and hence
`p_c < p_u`, bypassing the openness obstruction behind every recorded death
(the condition is closed under limits, so it needs no uniformity in `n`).

On `T_d` it works: `tau_p(o,x) = p^|x|`, so `a_n` is a positive combination of
`p^k`. Hence `log lambda` is convex in `t = log p`: it is flat at `log rho` up to
`p_2 = (d-1)^(-1/2)`, then equals `log((d-1)e^t + e^(-t)) - log d`.

## 1. Four universal facts about the profile of `lambda`

`G` is a nonamenable Cayley graph, `rho < 1` its spectral radius,
`a_n(p) = E tau_p(o, X_n)`, and `lambda(p) = lim a_n^(1/n)`.

* (F1) `lambda(p) = rho` on `(0, p_c]`. Lower bound: `a_(2n) >= p_(2n)(o,o)`,
  whose rate is `rho` (Kesten). Upper bound: `a_n` is nondecreasing in `p`, and
  Schramm's lemma gives `a_n(p_c) <= rho^n` (`fpbs-critical-walk-correlation`).
  Also `p_c > 0` (`p_c >= 1/(deg-1)`), so this is a nondegenerate interval.
* (F2) `lambda(p) >= p`, since `|X_n| <= n` and a geodesic is open with
  probability at least `p^n`. So `lambda(p) > rho` for `p > rho`, and
  `lambda -> 1` as `p -> 1`.
* (F3) If `p_u < 1`, then `lambda = 1` on `(p_u, 1)`. Uniqueness holds on all of
  `(p_u, 1]` (Haggstrom–Peres, Schonmann: uniqueness is monotone). Under
  uniqueness Harris–FKG gives `tau_p(o,x) >= theta(p)^2 > 0`, so `a_n >= theta^2`.
  This is the same floor as step 7 of `fpbs-lq-two-point-bounds-walk-rate-proof`.
* (F4) `lambda` is nondecreasing, and `lambda <= 1`.

## 2. Plateau lemma

**Lemma.** Let `f` be a real function on an interval `J`. Suppose `f` is constant
`= c` on a nondegenerate subinterval `I` of `J`.

1. If `f` is concave and `f(s) > c` for some `s` in `J`, contradiction.
2. If `f` is convex and `f(s) < c` for some `s` in `J`, and `f <= c` on `J`,
   contradiction.

**Proof.** Pick `m` in the interior of `I`. Pick `e` in `I` with `m` strictly
between `e` and `s`. This is possible because `m` is interior. Write
`m = theta e + (1-theta) s` with `theta` in `(0,1)`.

1. Concavity gives `c = f(m) >= theta c + (1-theta) f(s) > c`.
2. Convexity gives `c = f(m) <= theta c + (1-theta) f(s) < c`.

In both cases this is a contradiction. QED.

## 3. Theorem

Let `phi : (0,1) -> J` be any homeomorphism onto an interval, of either
orientation. Let `psi` be any strictly increasing function on `[rho, 1]`. Put
`f = psi o lambda o phi^(-1)`.

* **(A) Concave shapes die on every nonamenable Cayley graph.** By (F1), `f` is
  constant `psi(rho)` on `phi((0, p_c])`. By (F2), `f > psi(rho)` near
  `phi(1^-)`. Part 1 of the Lemma applies.
* **(B) Convex shapes die on every nonamenable Cayley graph with `p_u < 1`.**
  This includes all one-ended planar hyperbolic Cayley graphs, surface groups,
  and every one-ended finitely presented nonamenable group (Babson–Benjamini,
  Timar: `p_u < 1`). By (F3), `f = psi(1) = max f` on `phi((p_u,1))`. By (F1),
  `f(phi(p_c)) = psi(rho) < psi(1)`. Part 2 of the Lemma applies.
* **(C) Convexity dies even when `p_u = 1`.** See Section 4: on
  `T_3 box K_2`, which has infinitely many ends, `p_u = 1` and `p_c < p_u`,
  `log lambda` is not convex in `log p` on `(0.70, 0.995)`.
* **(D) Restricting the domain is circular.** Suppose a shape condition is
  imposed only on a domain defined from the percolation, such as `{lambda < 1}`,
  `(0, p_u)` or `(0, p_lambda)` with `p_lambda = inf{lambda = 1}`. In the
  collapse scenario (`p_c = p_u`, `lambda = 1` on `(p_c, 1)`) that domain is
  `(0, p_c]` or `(0, p_c)`. On it, `lambda` is constant, which is convex and
  concave at once. So the condition holds in the collapse scenario and cannot
  exclude it.

**Corollary (finite-n form).** `log a_n^(1/n) -> log lambda` pointwise on
`(0,1)`: by Fekete the limit exists, and `a_n >= p^n > 0`. Convexity and
concavity are preserved under pointwise limits. So on every graph as in (A),
the functions `psi o a_n^(1/n) o phi^(-1)` are not all concave for large `n`.
The same holds for convexity on every graph as in (B) or (C). Hence no proof
of (IS) can go through a convexity or concavity statement about the finite
connection functions `a_n`, whatever the parametrisation. The Möbius
coefficients of connection events have mixed signs, so there is no nonnegative
log-sum-exp representation. Section 4 shows that this sign obstruction really
does bite on a Cayley graph.

## 4. Exact computation on `T_3 box K_2`

This is an infinite-volume version of the exact gadget and transfer reduction
in `experiments/fpbs-zg-ladder-zeros-2026-09-17/ladder_connectivity.py`. Side
gadgets converge to the least fixed point `h*` of
`h = p^2 (1 - (1-p)(1-h)^2)`. Along the geodesic,
`tau((v_k,i)) = c_i mu(p)^k (1+o(1))`, where `mu(p)` is the Perron root of the
3-state ladder transfer with rung `1 - (1-p)(1-h*)`. The tree distance of
simple random walk is the reflected chain with steps `+1, -1, 0` taken with
probabilities `1/2, 1/4, 1/4`. So

`lambda(p) = rho` if `mu <= 2^(-1/2)`, and `lambda(p) = 1/4 + mu/2 + 1/(4 mu)`
otherwise, with `rho = 1/4 + 2^(-1/2)`.

The formula passes three checks (script `experiments/fpbs-is-convexity-2026-09-17/lambda_shape.py`):

* The point where `mu = 2^(-1/2)` is `0.52620`, which is the recorded `p_2`.
* The ratios `(a_800/a_400)^(1/400)` of exact polynomials match `lambda` to
  six digits at `p = 0.6, 0.75, 0.9`. For example, at `p = 0.9` both give
  `0.997447`.

The second divided differences of `log lambda` in `log p` are negative on
`p in (0.702, 0.995)`, with minimum `-0.49` near `p = 0.995`. The mechanism
is two parallel rails. The data give `1 - mu ~ (1-p)^2`: `1 - mu(0.95) = 0.0025`
and `1 - mu(0.99) = 1.0e-4`. Also `psi'(1) = 1/4`. Hence
`log lambda ~ -c (log p)^2` near `p = 1`, which is locally concave.

So `log lambda` is convex, then concave: it is neither. This is a computation
with an exactly derived formula checked against the exact finite-`n`
polynomials, not a written proof of the asymptotics. Statements (A), (B) and
(D) do not depend on it.

## 5. Invariant and where every member dies

**Invariant.** The profile of `lambda` has two forced plateaus.

* The subcritical plateau `lambda = rho` on `(0, p_c]` (Schramm + Kesten).
  Every concave shape dies here.
* The saturation plateau `lambda = 1` on `(p_u, 1)` (the `theta^2` floor)
  whenever `p_u < 1`. Every convex shape dies here. On `T_3 box K_2`,
  convex shapes also die at the near-plateau `1 - lambda = O((1-p)^2)` created
  by parallel routes.

**Only escape.** A usable shape class would have to be closed under pointwise
limits, contain profiles with both plateaus and continuous ramps between them,
and still exclude the collapse profile. Any class that contains the ramps
`f_k = log rho` on `(0, p_c]`, linear to `0` on `[p_c, p_c + 1/k]` and `0`
after, for all `k`, contains their pointwise limit, which is the collapse
profile. So a closed shape route to (IS) must fix a quantitative slope bound
at `p_c`. That is a modulus-of-continuity statement, i.e. a form of (IS) with
a rate, or the pointwise budget `fpbs-pivotal-budget-universal`.
