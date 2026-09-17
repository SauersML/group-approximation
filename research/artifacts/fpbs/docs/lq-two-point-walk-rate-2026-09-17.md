# l^q two-point functions bound the walk connectivity rate (2026-09-17)

Author: swarm-0917-w5-pull2-fpbs-1 (transplanter, linear-characteristic family).

## 1. Setting and notation

- `G` is a connected, locally finite, transitive graph with root `o`.
- `P` is the simple random walk operator, `rho = ||P||_{2->2}`, and
  `p_n(o,x) = P(X_n = x)`.
- `tau_p(o,x) = P_p(o <-> x)`.
- `a_n(p) = P_p(o <-> X_n) = sum_x p_n(o,x) tau_p(o,x)`, where the walk is
  independent of the percolation.
- `lambda(p) = lim_n a_n(p)^(1/n)`, as in Section 6 of
  `research/artifacts/fpbs/exploration-pivotal-projections.md`.
- For `q >= 1` let `Z_q(p) = sum_x tau_p(o,x)^q` and
  `p_q = sup{p : Z_q(p) < infinity}`.
- `p_{q->q}` is the operator threshold of Hutchcroft arXiv:1804.10191:
  the supremum of `p` with `||T_p||_{q->q} < infinity`, where
  `T_p f(x) = sum_y tau_p(x,y) f(y)`.

## 2. Supermultiplicativity (constant-free Fekete)

**Lemma 2.1.** `a_{n+m}(p) >= a_n(p) a_m(p)`.

*Proof.*

1. The events `{o <-> x}` and `{x <-> z}` are increasing. By Harris-FKG,
   `tau(o,z) >= P(o <-> x, x <-> z) >= tau(o,x) tau(x,z)`.
2. Condition on `X_n = x`. By the Markov property the remaining `m` steps
   start at `x`, and transitivity gives `sum_z p_m(x,z) tau(x,z) = a_m`.
3. So `a_{n+m} >= sum_x p_n(o,x) tau(o,x) a_m = a_n a_m`.

By Fekete, `lambda = sup_n a_n^(1/n)`. In particular `a_n <= lambda^n` and
`a_n <= a_{kn}^(1/k)` for every `k >= 1`. QED.

**Lemma 2.2.** `lambda(p) >= rho` for every `p`.

*Proof.* `a_{2n} >= p_{2n}(o,o) tau(o,o) = p_{2n}(o,o)`, and
`p_{2n}(o,o)^(1/2n) -> rho` by Kesten. QED.

## 3. The l^q interpolation bound

**Theorem 3.1.** Let `q >= 2` and `Z_q(p) < infinity`. Then
`a_n(p) <= rho^(2n/q)` for all `n >= 0`, so `lambda(p) <= rho^(2/q)`.

*Proof.*

1. **Hölder.** With `1/q + 1/q' = 1`,
   `a_n <= ||p_n(o,.)||_{q'} ||tau_p(o,.)||_q = ||p_n(o,.)||_{q'} Z_q^(1/q)`.
2. **Log-convexity of l^r norms (Riesz-Thorin for one function).** Put
   `theta = 2/q`, which lies in `(0,1]`. Then
   `1/q' = (1 - theta)/1 + theta/2`, so
   `||f||_{q'} <= ||f||_1^(1-theta) ||f||_2^theta`.
3. **Heat kernel.** `||p_n(o,.)||_1 = 1`. Also
   `||p_n(o,.)||_2^2 = sum_x p_n(o,x) p_n(x,o) = p_{2n}(o,o) <= rho^(2n)`,
   using that simple random walk on a regular graph is symmetric.
   Hence `||p_n(o,.)||_{q'} <= rho^(n theta) = rho^(2n/q)`.
4. So `a_n <= Z_q^(1/q) rho^(2n/q)` for every `n`.
5. **Removing the constant.** By Lemma 2.1,
   `a_n <= a_{kn}^(1/k) <= Z_q^(1/(qk)) rho^(2n/q)`. Let `k -> infinity`. QED.

**Corollary 3.2.**

1. `lambda(p) = rho` for every `p <= p_2`. For `p < p_2` this follows from
   Theorem 3.1 with `q = 2` and Lemma 2.2.
2. At `p = p_2` itself the claim holds even if `Z_2(p_2) = infinity`:
   - `a_n(p) = sum_{|x| <= n} p_n(o,x) tau_p(o,x)` is a finite sum;
   - each `tau_p(o,x)` is left-continuous in `p` (it is an increasing limit
     of connection probabilities inside balls);
   - so `a_n(p_2) = lim_{p up to p_2} a_n(p) <= rho^n`.
3. For `p <= p_q` with `q >= 2`, we get `lambda(p) <= rho^(2/q)`, by the same
   left-continuity at `p_q`.

**Corollary 3.3 (trivial nonuniqueness certificate).** Suppose `rho < 1` and
some `p` has `Z_q(p) < infinity` for some finite `q`. Then `lambda(p) < 1`.
Under uniqueness `a_n >= theta(p)^2`, which forces `lambda = 1`. So
`theta(p) = 0` or there are infinitely many infinite clusters, and in
particular `p <= p_u`.

**Remark 3.4 (the q = 2 case recovers Hutchcroft).** Theorem 3.1 with `q = 2`
gives `E tau_p(X_0,X_n) <= rho^n` for `p <= p_2`. Since `p_{2->2} <= p_2`,
this contains Hutchcroft arXiv:1804.10191v3, Proposition
prop:nonuniquenessatpell2 (quoted in Section 8), whose hypothesis is
`p <= p_{2->2}`. Hutchcroft's proof applies Cauchy-Schwarz to the operators.
The proof here applies Cauchy-Schwarz to the vector `tau_p(o,.)` and so needs
only `tau_p(o,.)` in `l^2`, not boundedness of `T_p`.

## 4. Thresholds and a new sufficient condition for (IS)

**Lemma 4.1 (ordering).** `p_{q->q} <= p_q` for every `q`, and
`p_c <= p_{2->2} <= p_2 <= p_q <= p_u` for every finite `q >= 2`, when
`rho < 1`.

*Proof.*

1. `||tau_p(o,.)||_q = ||T_p delta_o||_q <= ||T_p||_{q->q}`.
2. `tau_p <= 1`, so `Z_2 < infinity` implies `Z_q < infinity`.
3. `p_q <= p_u` follows from Corollary 3.3, using monotonicity of `Z_q` in `p`
   and left-continuity.

`p_c <= p_{2->2}` holds because `T_p` is unbounded above `p_c`: there
`chi_p = infinity` gives `||T_p 1_{B_R}||_2 / ||1_{B_R}||_2 -> infinity`, as in
Hutchcroft 1804.10191. QED.

**Theorem 4.2 (route to IS).** Suppose `p_c < p_q` for every `q > 2`, which
is hypothesis [Q]. Then `lambda(p)` decreases to `rho` as `p` decreases to
`p_c`. By the rate identity of `fpbs-integrated-pivotal-rate-identity`
(Section 6 of exploration-pivotal-projections.md), this is (IS).

*Proof.*

1. `lambda` is nondecreasing in `p`, and `lambda >= rho` by Lemma 2.2.
2. Given `q > 2`, pick `p' in (p_c, p_q)`. Then `Z_q(p') < infinity`.
3. So for all `p in (p_c, p']`, `rho <= lambda(p) <= lambda(p') <= rho^(2/q)`.
4. Hence `limsup_{p down to p_c} lambda(p) <= rho^(2/q)`. Let `q` decrease
   to 2. QED.

**Comparison.**

- [Q] is implied by `p_c < p_{2->2}` (Lemma 4.1). That is the hole
  `fpbs-nonamenability-bounds-critical-connectivity-operator`, which is known
  for the Hutchcroft classes.
- [Q] asks only that the single vector `tau_p(o,.)` be in `l^q` slightly
  above `p_c`, for each `q > 2`. Boundedness of the operator is not needed.
- [Q] also tolerates `Z_2(p) = infinity` for all `p > p_c`.
- It is incomparable a priori with the sphere-rate hypothesis EG of
  `fpbs-sphere-two-point-rate-right-continuous-universal`:
  - EG controls sphere masses `E|K_o ∩ S_r|`, which count exponential volume;
  - [Q] controls `sum_r sum_{x in S_r} tau^q`, which can be finite while `M_r`
    grows exponentially.

**Negation of [Q].** [Q] fails iff there is `q > 2` with `Z_q(p) = infinity`
for every `p > p_c`, i.e. `p_q = p_c`. Since `Z_q` is nonincreasing in `q`,
the same then holds for every `q' in (2, q]`. A counterexample to [Q] is thus
a nonamenable Cayley graph with some `q_0 > 2` such that
`q_c(p) := inf{q : Z_q(p) < infinity} >= q_0` for all `p > p_c`.

## 5. Calibration on regular trees

On `T_d`:

- `tau_p(o,x) = p^|x|`;
- `Z_q(p) < infinity` iff `(d-1) p^q < 1`, so `p_q = (d-1)^(-1/q)`;
- `p_c = 1/(d-1) < p_q` for every finite `q`, so [Q] holds.

The exact walk rate is `lambda(p) = rho` for `p <= 1/sqrt(d-1)`, and
`((d-1)p + 1/p)/d` above. Theorem 3.1 is therefore sharp on the whole flat
range `[0, p_2]`. For comparison, `rho cosh(g_+)` with
`g = log((d-1)p)` exceeds `rho` on all of `(p_c, p_2]`.

`experiments/lq-two-point-walk-rate-2026-09-17/tree_check.py` (output in
`tree_check.out`, exit 0) computes `a_n(p) = E p^{|X_n|}` exactly for
`d = 3, 4, 6` and `n <= 400`. It checks `a_n <= rho^(2n/max(2,q_c))` with
constant 1 at five parameters per tree.

## 6. Calibration: a flat rate is strictly weaker than both criteria

Let `Gamma` be nonamenable and `H <= Gamma` an infinite amenable subgroup.
Take the kernel `t = 1_H`. This is a test kernel for the linear functional
`t -> sum_x p_n(o,x) t(x)`, not a percolation two-point function.

1. `sum_x p_n(o,x) 1_H(x) = P(X_n in H)` is the return probability of the
   projected walk on the Schreier graph `H \ Gamma`. Its exponential rate is
   the spectral radius of that Schreier graph.
2. It is at least `rho(Gamma)`, since `X_n = e` implies `X_n in H`.
3. It is at most `rho(Gamma)`: the quasi-regular representation on
   `ell^2(H \ Gamma)` is weakly contained in the regular representation when
   `H` is amenable (Eymard, Greenleaf). This is a standard fact and is used
   here only as calibration.
4. So the rate is exactly `rho`. Yet `1_H` is not in any `l^q` for finite `q`,
   and convolution by `1_H` is unbounded on `l^2`.

Hence "rate `rho`" does not force `l^q` summability or operator boundedness.
Neither criterion is necessary for the functional conclusion, so a failure of
[Q] would not by itself refute (IS).

## 7. Where the route stops

**S1 (openness of `{Z_q < infinity}` through `p_c`).** The natural
differential inequality is Russo plus BK:
`d/dp tau_p(o,x) <= sum_{(u,v)} tau_p(o,u) tau_p(v,x)`. It gives
`d/dp Z_q <= q sum_x tau(o,x)^(q-1) sum_{(u,v)} tau(o,u) tau(v,x)`.

Closing it needs a bounded triangle-type or operator quantity. Above `p_c`,
`chi_p = infinity`, and the mixed sum is not controlled by `Z_q` alone. This
is the obstruction of `fpbs-bk-majorant-integrated-sensitivity-is-critical-l2`:
every BK majorant of the derivative is a critical `l^2`-type quantity.

**S2 (no importable critical `l^q` input).** Even `Z_q(p_c) < infinity` for
some finite `q` is not available in general. Hutchcroft arXiv:1605.05301v1,
Theorem thm:pcconnectivitydecay (Section 8), bounds only the infimum
`kappa_{p_c}(n)` over pairs at distance at most `n`. That does not bound
`tau_{p_c}(o,x)` for typical `x` in `S_n`, so it gives no sphere sum.

**Citation spark.** The EG0 bullet of
`research/fpbs-sphere-two-point-rate-right-continuous-universal.md` attributes
a pointwise bound `tau_{p_c}(o,x) <= gr^{-|x|}` to arXiv:1603.00555. That id
is a different paper. The critical-decay theorem is arXiv:1605.05301, and as
quoted in Section 8 it bounds only the infimum `kappa_{p_c}(n)`. So the
upper half of EG0 (`g(p_c) <= 0`) has no import as stated. Also, even a
pointwise bound `gr^{-|x|}` would only give `M_r(p_c) <= |S_r| gr^{-r}`, which
has rate `0`, matching EG0, but that pointwise bound is not the theorem.

## 8. Verbatim citations

**[H18]** T. Hutchcroft, arXiv:1804.10191v3, Proposition
prop:nonuniquenessatpell2 (source HyperbolicPercolation6.tex):

> Let $G$ be a connected, locally finite, transitive, nonamenable graph, let
> $X$ be simple random walk on $G$, and let $\rho(G)<1$ be the spectral radius
> of $G$. Then \[\E\left[ \tau_p(X_0,X_n) \right] \leq \rho(G)^{n}\] for every
> $0\leq p \leq p_{2\to2}$.

**[H16]** T. Hutchcroft, arXiv:1605.05301v1, Theorem thm:pcconnectivitydecay
(source expperc.tex):

> Let $G$ be a quasi-transitive graph with exponential growth. Then
> \[\kappa_{p_c}(n):= \inf\left\{\tau_{p_c}(x,y) : x, y \in V,\, d(x,y) \leq n
> \right\}\leq \mathrm{gr}(G)^{-n}\] for all $n\geq1$.

Theorem 3.1 and Theorem 4.2 use neither citation as a premise. [H18] is quoted
for comparison (Remark 3.4), and [H16] for S2 and the spark.
