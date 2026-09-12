# HS median assembly: (H1) + (H2') force (CCR) and normalization (2026-09-12)

Lane `hs-s4-assembly`. This writes step S4 of `research/artifacts/hs-scale-pinning-2026-09-12.md`
and closes the corrected conditional of `hs-normalization-needs-coarse-actor-scale-pinning`.
Result: the claim `hs-rounding-and-actor-gap-force-ccr` (ESTABLISHED) with open inputs
`hs-stable-vertex-rounding-for-every-model` (H1) and `hs-coarse-actor-gap-at-compressor-generators`
(H2').

Two points differ from the scale-pinning sketch.
- **No block-by-block transport.** The per-scale transport estimate of
  `vertex-rounding-reduces-ccr-to-commutant-excess` (item 4) is uniform in `a` only in the global
  2-norm, so it cannot be summed over blocks that each use their own scale. S4 instead uses an
  exact operator inequality through the intertwiner (section 3), valid for all `a` at once, whose
  error factors through one small operator.
- **The center clause must be block-dependent.** Clause (H2')(c) asks almost commutation with
  every family of central contractions chosen block by block. The fixed-`a` form of the sketch is
  not enough (section 6).

## 0. Setting and hypotheses

- `Gamma < G` infranormal Kazhdan pair, `(F, kappa)` a Kazhdan pair for `Gamma`.
- `t_1, ..., t_k` strict compressors with `G = <Gamma, t_1, ..., t_k>`, `Lambda_i = t_i Gamma t_i^(-1)`.
- `S = F cup {t_i^(+-1)}`.
- `sigma : G -> U(M)` trace-preserving, `M = prod_U M_n`, coordinates `sigma_n`.

**(H1)** After `o(n)` padding there are genuine `pi_n : Gamma -> U(n')`, `n'/n -> 1`, with
`max_(s in F) ||sigma_n(s) - pi_n(s)||_2 -> 0`. Padding changes every 2-norm below by `o(1)`, and
all objects are taken in `M_(n')`.

**(H2')** Along `U` there are orthogonal projections `q_A` (`A` in a finite set `I_n`), with
`p = sum_A q_A` and `q_0 = 1 - p`, such that:
- (a) `tau(q_0) -> 0` and `sum_A ||[sigma_n(s), q_A]||_2^2 -> 0` for each `s in S`;
- (b) there is `kappa' > 0` such that for every `A` and every self-adjoint `x in q_A M_(n') q_A`,
  `sum_(s in S) ||a_(A,s) x - x a_(A,s)||_(2,q_A)^2 >= kappa'^2 ||x - tau_(q_A)(x) q_A||_(2,q_A)^2`,
  where `a_(A,s) = q_A sigma_n(s) q_A`;
- (c) `sup { sum_A ||[q_A, z_A]||_2^2 : z_A in Z(pi_n(Gamma)'), ||z_A|| <= 1 } -> 0`.

**Theorem.** Under (H1) and (H2'), `sigma(Lambda_i)' cap M = sigma(Gamma)' cap M` for each `i`,
and `sigma(G)` normalizes `sigma(Gamma)' cap M`.

## 1. Notation and elementary facts

- `A_n = pi_n(Gamma)'`. For a fixed compressor `t = t_i`: `Lambda = Lambda_i`, `B_n = pi_n(Lambda)'`.
- `zeta_A, zeta_B`: the aspect-ratio observables of `A_n, B_n`, as in
  `vertex-rounding-reduces-ccr-to-commutant-excess`. They are central in `A_n`, `B_n` respectively,
  commute, and `zeta_B >= zeta_A` (`commutant-excess-jump-mass-proof`, Monotonicity).
- `F_a(x) = x/(x+a)`, `h_a = F_a(zeta_A)`, `k_a = F_a(zeta_B)`. Then `0 <= h_a <= k_a <= 1`, and
  `h_a in Z(A_n)`, so `pi_n(s) h_a pi_n(s)^* = h_a` for `s in Gamma`.
- (F) `0 <= F_a(x) - F_a(x/lambda) <= (1/4) log lambda` for `lambda >= 1`, since `x F_a'(x) <= 1/4`.
  With `lambda = 1 + c`, the defect is at most `c/4`.
- `beta(u)^2 = sum_(A in I_n) ||[u, q_A]||_2^2 + 4 tau(q_0)`, which tends to `0` for `u = sigma_n(s)`, `s in S`,
  by (H2')(a), because `||[u, q_0]||_2 <= 2 tau(q_0)^(1/2)`.

## 2. Two summation lemmas

**L1 (block replacement).** For a unitary `u`, `p_A = u q_A u^*` (including `A = 0`) and contractions
`X_A`:
`||sum_A p_A X_A p_A - sum_A q_A X_A q_A||_2 <= 2 beta(u)`.

*Proof.* The difference is `sum_A (p_A - q_A) X_A p_A + sum_A q_A X_A (p_A - q_A)`. In the first sum
the right factors `p_A` are orthogonal, so its squared 2-norm is `sum_A ||(p_A - q_A) X_A p_A||_2^2
<= sum_A ||p_A - q_A||_2^2`. The second sum is the same with left factors `q_A`. Finally
`||p_A - q_A||_2 = ||[u, q_A]||_2`.

**L2 (one-sided errors sum).** If `Y_A = W X_A Z_A + X'_A W'` with contractions `X_A, Z_A, X'_A`, then
`||sum_A q_A Y_A q_A||_2^2 <= 2 (||W||_2^2 + ||W'||_2^2)`.

*Proof.* The blocks are orthogonal on both sides, so the squared norm is
`sum_A ||q_A Y_A q_A||_2^2 <= 2 sum_A (||q_A W||_2^2 + ||W' q_A||_2^2)`, and
`sum_A ||q_A W||_2^2 = ||W||_2^2`, `sum_A ||W' q_A||_2^2 = ||W'||_2^2`.

The point of L2: the errors may depend on `A` through `X_A, X'_A, Z_A`, but the small factor
`W`, `W'` must not.

## 3. The exact compressor inequality

Fix `t`. By item 3 of `vertex-rounding-reduces-ccr-to-commutant-excess` there are partial isometries
`v` with `v pi_n(lambda) = pi~_n(lambda) v` for `lambda in Lambda` and `||v - 1||_2 -> 0`, where
`pi~_n(lambda) = sigma_n(t) pi_n(t^(-1) lambda t) sigma_n(t)^*`. Put `zeta~ = sigma_n(t) zeta_A sigma_n(t)^*`.

- `vv^* in pi~_n(Lambda)'` and `v^* v in B_n` (intertwiners).
- `pi~_n(Lambda)' = sigma_n(t) A_n sigma_n(t)^*`, so `zeta~` is central there: it equals `m_i/d_i` on the
  isotypic component of the transported irreducible `rho_i o Ad t^(-1)`.
- `v` carries the `theta_j`-isotypic part of `v^* v` into the equivalent isotypic component of `pi~_n`.
  Hence `v^* F_a(zeta~) v = F_a(zeta^) v^* v`, where `zeta^ = m_(iota(j))/e_j` on type `j` and
  `iota(j)` is the transported type equivalent to `theta_j`. `zeta^` is central in `B_n`.
- Let `r_j` be the multiplicity of `theta_j` in `v^* v`, so `r_j <= m_(iota(j))` and `r_j <= m'_j`.
  For `c in (0,1)` let `R_c` be the sum of the minimal central projections `w_j` of `B_n` with
  `r_j < m'_j/(1+c)` (including `r_j = 0`). On type `j` the projection `1 - v^* v` has mass
  `(m'_j - r_j) e_j / n' >= (c/(1+c)) m'_j e_j / n'`, so `tau(R_c) <= ((1+c)/c) tau(1 - v^* v)`.
  Also `tau(1 - v^* v) = ||1 - v^* v||_2^2 <= 4 ||v - 1||_2^2`.
- Put `Q = v^* v (1 - R_c)`. Off `R_c`, `zeta^ >= m'_j/((1+c) e_j) = zeta_B/(1+c)`.

**L3.** For every `a > 0`:

```text
F_a(zeta~)  >=  v Q k_a Q v^* - c/4  >=  v Q h_a Q v^* - c/4.
```

*Proof.*
1. `F_a(zeta~)` commutes with `vv^*` and is positive, so `F_a(zeta~) >= vv^* F_a(zeta~) vv^* = v F_a(zeta^) v^*`.
2. `F_a(zeta^)`, `F_a(zeta_B/(1+c))`, `R_c`, `v^* v` commute. On `Q`, `F_a(zeta^) >= F_a(zeta_B/(1+c))`; on
   `v^* v R_c` the left side is `>= 0`. So `F_a(zeta^) v^* v >= Q F_a(zeta_B/(1+c)) Q`, and conjugating
   by `v` gives `v F_a(zeta^) v^* >= v Q F_a(zeta_B/(1+c)) Q v^*`.
3. By (F), `F_a(zeta_B/(1+c)) >= k_a - c/4`, and `v Q v^* <= 1`. This is the first inequality.
4. `k_a >= h_a` (commuting, `zeta_B >= zeta_A`), and compression preserves order. This is the second.

Write `W = vQ - 1`. Then `||W||_2 <= ||v v^* v R_c||_2 + ||v - 1||_2 <= tau(R_c)^(1/2) + ||v - 1||_2`, which
tends to `0` for each fixed `c`. For any contraction `X`, `v Q X Q v^* - X = W X Q v^* + X W^*`, the
shape required by L2.

## 4. The median observable (S4)

For `A in I_n` let `N_A = rank q_A`. The sorted eigenvalues of `q_A h_a q_A` on `q_A` are continuous
in `a`, tend to `1` as `a -> 0` (`zeta_A >= 1/n'`) and to `0` as `a -> infinity`. Choose `m_A > 0` with
`lambda_(ceil(N_A/2)) (q_A h_(m_A) q_A) = 1/2`. Since `lambda_(floor(N_A/2)+1) >= lambda_(ceil(N_A/2))`, `1/2` is a
median of `q_A h_(m_A) q_A` for `tau_(q_A)`. Put

```text
f   = sum_A q_A h_(m_A) q_A + (1/2) q_0,
f_B = sum_A q_A k_(m_A) q_A + (1/2) q_0.
```

Then `f` commutes with every `q_A` and `q_0`, and `0 <= f <= f_B <= 1`.

**Vertex generators.** For `s in F` put `D = sigma_n(s) - pi_n(s)`. For `h in Z(A_n)`,
`sigma_n(s) h sigma_n(s)^* - h = D h sigma_n(s)^* + pi_n(s) h D^*`. By L1 with `u = sigma_n(s)` and then L2,

```text
||sigma_n(s) f sigma_n(s)^* - f||_2  <=  2 beta(sigma_n(s)) + 2 ||sigma_n(s) - pi_n(s)||_2  ->  0.
```

**Compressor.** Let `G_t = sum_A q_A F_(m_A)(zeta~) q_A + (1/2) q_0`. Since
`sigma_n(t) f sigma_n(t)^* = sum_A p_A F_(m_A)(zeta~) p_A + (1/2) p_0`, L1 gives
`||sigma_n(t) f sigma_n(t)^* - G_t||_2 <= 2 beta(sigma_n(t))`, hence `tau(G_t) <= tau(f) + 2 beta`. Compressing L3
by `q_A` with `a = m_A` and summing (block `q_0` is identical on all sides):

```text
G_t >= f   + Y  - c/4,     Y  = sum_A q_A (v Q h_(m_A) Q v^* - h_(m_A)) q_A,
G_t >= f_B + Y' - c/4,     Y' = sum_A q_A (v Q k_(m_A) Q v^* - k_(m_A)) q_A.
```

By L2, `||Y||_2, ||Y'||_2 <= 2 ||W||_2`, and `||Y||, ||Y'|| <= 4`.
- *Trace of `f_B - f`.* `tau(f_B) <= tau(G_t) + |tau(Y')| + c/4 <= tau(f) + 2 beta + 2 ||W||_2 + c/4`.
- *Almost invariance.* `N = G_t - f - Y + c/4 >= 0` has `tau(N) <= 2 beta + 2 ||W||_2 + c/4` and
  `||N|| <= 7`, so `||N||_2^2 <= 7 tau(N)`. Since `sigma_n(t) f sigma_n(t)^* - f = (sigma_n(t) f sigma_n(t)^* - G_t) + N + Y - c/4`,

```text
||[sigma_n(t), f]||_2  <=  2 beta + (7 (2 beta + 2 ||W||_2 + c/4))^(1/2) + 2 ||W||_2 + c/4.
```

`f` and `f_B` do not depend on `c`. Letting `n -> U` and then `c -> 0`:
`lim_U ||[sigma_n(t), f]||_2 = 0` and `lim_U tau(f_B - f) = 0`. The same holds for `t^(-1)` by unitary invariance.

## 5. Concentration (S5)

Apply `median-poincare-concentration` on each block `q_A`, with the tuple `a_(A,s)` of (H2')(b) and
`f_A = q_A f q_A` (median `1/2`). As `f` commutes with `q_A`, `a_(A,s) f_A - f_A a_(A,s) = q_A [sigma_n(s), f] q_A`.
Multiplying by `tau(q_A)` and summing over `A`, since block compressions are orthogonal:

```text
||f - 1/2||_2^2  <=  ((1 + sqrt 2)^2 / kappa'^2) sum_(s in S) ||[sigma_n(s), f]||_2^2  ->  0.
```

## 6. Jump mass and (CCR) (S6)

Let `J_c = 1(zeta_B >= (1+c) zeta_A)` (commuting functional calculus). Pointwise on the joint
spectrum, for every `m > 0`:

```text
J_c  <=  1(|h_m - 1/2| > 1/4) + (28/(3c)) (k_m - h_m).
```

If `|F_m(x) - 1/2| <= 1/4` then `rho = x/m in [1/3, 3]`. If moreover `y >= (1+c) x`, then
`F_m(y) - F_m(x) >= c rho / ((1 + (1+c) rho)(1 + rho))`. This is unimodal in `rho`, and its values at
`rho = 1/3, 3` are at least `3c/20` and `3c/28` for `c <= 1`.

Compress by `q_A` with `m = m_A`, take traces, and sum:

```text
tau(J_c)  <=  tau(q_0) + 16 sum_A ||(h_(m_A) - 1/2) q_A||_2^2 + (28/(3c)) tau(f_B - f),
||(h_(m_A) - 1/2) q_A||_2^2  =  ||q_A (h_(m_A) - 1/2) q_A||_2^2 + ||(1 - q_A)[h_(m_A), q_A]||_2^2.
```

The first pieces sum to `||f - 1/2||_2^2`, which tends to `0` by section 5 (on `q_0`, `f = 1/2`). The second sum to at most
`sum_A ||[q_A, h_(m_A)]||_2^2`, which tends to `0` by (H2')(c), because `h_(m_A)` is a central contraction of
`A_n` chosen block by block. With section 4, `lim_U tau(J_c) = 0` for every `c in (0,1)`.

By `commutant-excess-bounded-by-aspect-ratio-jump-mass`, `eps_n <= 4 tau(J_c)^(1/2) + 2c`, so
`lim_U eps_n <= 2c` for every `c`. Hence `lim_U eps_n = 0`, and item 2 of
`vertex-rounding-reduces-ccr-to-commutant-excess` gives (CCR) for `Lambda_i`.

**Normalization.** `Ad sigma(t_i)` maps `sigma(Gamma)' cap M` onto `sigma(Lambda_i)' cap M`, which by (CCR) equals
`sigma(Gamma)' cap M`. `sigma(Gamma)` fixes it pointwise, and `G = <Gamma, t_i>`. QED.

**Why (c) is block-dependent.** A rank-one block on `psi = (e_1 + e_2)/sqrt 2`, with `e_1, e_2` in
isotypic components where `h_m = 0.2` and `0.8`, has `q h_m q = (1/2) q` while no mass lies within a
factor `3` of `m`. Compressed concentration controls spectral mass only through `[q_A, h_(m_A)]`,
and the scale `m_A` varies with the block.

## 7. What stays open

- (H1): `hs-stable-vertex-rounding-for-every-model`.
- (H2'): `hs-coarse-actor-gap-at-compressor-generators`.
- A multiplicity cascade with order-one jump mass under (H1) refutes (H2'), by the theorem and the
  excess lemma.
- Route into `kt-centralizer-normalization-hs`: `hs-normalization-via-vertex-rounding-and-actor-gap`.
