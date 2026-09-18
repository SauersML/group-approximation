# Two-sided threshold-rank gate for Gap-SSE: attempted route (2026-09-17)

Date: 2026-09-17, swarm-0917. Target claim:
`sse-reductions-need-high-threshold-rank-on-both-sides` (OPEN).

**Status: attempt, not a route.** This file was posted as the route
`sse-two-sided-rank-gate-proof` with `requires: []`. Referee review (2026-09-18,
import-fidelity lens) refuted the claim **as stated** at the `(G-comb)` bullet of
its gate: the two combinatorial kills it imports are quoted with the wrong
quantifiers for the regular exact-volume convention this claim works in (details
in the `## Attempts` section of the claim file). The claim was returned to OPEN
and this file was demoted out of the compiled graph, so it establishes nothing.

Two other referee lenses re-derived Theorems 1--3 and sections (1)--(11) below
independently and found no failing step, and the replay
`experiments/sse-two-sided-rank-gate-2026-09-17/check_two_sided_rank_gate.py`
prints ALL PASS. So the spectral content is kept verbatim as the substance of the
attempt; what is not kept is the claim that it is proved. Section (12) also
carries a separate, non-fatal scoping error flagged by the calibration lens: the
abelian-Cayley "survivor" annotation is witnessed only on the YES side, and the
noisy hypercube is an abelian Cayley graph that `(K2)` kills as a NO output.

Whoever picks this up needs: a corrected `(G-comb)` import at exact volume, and a
narrowed section (12).

Artifact: `experiments/sse-two-sided-rank-gate-2026-09-17/check_two_sided_rank_gate.py`.

---

Notation is as in the target claim. Only finite-dimensional linear algebra is
used:

- the spectral theorem for real symmetric matrices;
- the fact that the sum of the `m x m` principal minors of a symmetric matrix is
  the `m`-th elementary symmetric function of its eigenvalues;
- Cramer's rule.

The inner product is the standard one, `<g, h> = sum_v g(v) h(v)`. `M` is
symmetric, so `A` and `B` are symmetric. `A` is stochastic, so its eigenvalues
lie in `[-1, 1]` and those of `B` lie in `[0, 1]`. There is an orthonormal
eigenbasis for both.

## (1) Rayleigh identity

Let `f = 1_S` with `|S| = s`. Then `||f||^2 = s` and `<f, A f> = e(S)/d = (1 - Phi(S)) s`.
So `<f, B f> = s (2 - Phi(S))/2` and `s - <f, B f> = s Phi(S)/2`.

## (2) Spectral split

Let `theta < 1`. Write `g = g_hi + g_lo`, where `g_hi` projects onto the
eigenvectors of `B` with eigenvalue `>= theta`. Then
`<g, B g> <= ||g_hi||^2 + theta ||g_lo||^2 = ||g||^2 - (1 - theta) ||g_lo||^2`.
With (1): `||f_lo||^2 <= s Phi(S) / (2 (1 - theta))`.

## (3) Threshold rounding

For `g : V -> Q` put `T = {v : g(v) >= 1/2}`.

*Claim.* `|T xor S| <= 4 ||g - f||^2` and `e(T) >= e(S) - 2 d |S \ T|`.

*Proof.*
- Every `v in T xor S` has `|g(v) - f(v)| >= 1/2`, which gives the first bound.
- `e(S) - e(S n T)` counts the pairs `(u, v)` in `S x S` with an endpoint in
  `S \ T`, weighted by `M`. That is at most `2 sum_(u in S \ T) sum_v M(u, v) = 2 d |S \ T|`.
- `e(T) >= e(S n T)` because `M >= 0`.

## (4) Window lemma

Put `rho(T) = (1 - Phi(T)) kappa(|T|)`, where `kappa(t) = t/s` for `t <= s` and
`kappa(t) = (s - 1)/(t - 1)` for `t > s`. Put `rho(emptyset) = 0`.

*Claim.* For every nonempty `T`, some `T'` with `|T'| = s` has `1 - Phi(T') >= rho(T)`.

*Proof.*
- If `t = |T| <= s`, take any `T' ⊇ T` with `|T'| = s`. Then `e(T') >= e(T)`, so
  `1 - Phi(T') >= e(T)/(d s) = (1 - Phi(T)) t/s`.
- If `t > s`, let `T'` be a uniformly random `s`-subset of `T`. A pair
  `u != v` in `T` survives with probability `s(s-1)/(t(t-1))`, and a loop
  `(u, u)` survives with probability `s/t`, which is at least that. So
  `E e(T') >= e(T) s(s-1)/(t(t-1))`, and some `T'` attains
  `e(T')/(d s) >= (e(T)/(d t)) (s-1)/(t-1)`.

## (5) Parameters and the algorithm

If `s < 100`, decide exactly by enumerating all `s`-sets: `n^99 poly(Z)`. No
"rank above" is output. Assume `s >= 100`, so `n >= 100`.

Fix `eta in (0, 1/800]`. Put:

- `gamma = 400 eta <= 1/2` and `theta_hi = 1 - gamma/8`;
- `L = ceil(log2 n)`, `tau = 2^(-40 - 6L)` and `t = ceil(0.7 (40 + 7L)/gamma)`.

Let `R = R(M) = rank_(1-800 eta)(A)`. Since `lambda_B = (1 + lambda_A)/2`, `R` is
the number of eigenvalues of `B` that are `>= 1 - gamma`.

*Algorithm.*

1. Compute `P = B^t` exactly, with columns `w_z = P 1_z`.
2. Start with the empty list (`i = 0`) and repeat. For every `z` compute the
   residual `res_z = w_z - sum_(l <= i) (<w_z, v_l>/<v_l, v_l>) v_l`.
   - If `max_z ||res_z||^2 <= tau`, stop (the **ordinary stop**) and go to step 3.
   - If `i = 2R*`, output "rank above `R*`".
   - Otherwise put `v_(i+1) = res_z` for the least maximizing `z`, and repeat.
3. Let `m = i`. For each `l`, let `e_l` be the integer with
   `4^(e_l) s <= ||v_l||^2 < 4^(e_l + 1) s`, and put `psi_l = 2^(-e_l) v_l`, so
   `sqrt(s) <= ||psi_l|| < 2 sqrt(s)`.
4. Let `h = 2^(-ceil(log2(sqrt(m + 1)/0.09)))`, so `h <= 0.09/sqrt(m + 1)`, and let
   `Lev = {-1 + jh : 0 <= j <= ceil(2/h)}`.
5. For every `dvec in Lev^m`, form `g = sum_l d_l psi_l` and `T = {v : g(v) >= 1/2}`,
   and compute `rho(T)`. Output ACCEPT iff some `rho(T) > eta`, else REJECT.

The `v_l` are pairwise orthogonal. `res_z = Q w_z`, where `Q` is the orthogonal
projection onto the complement of `span(v_1, ..., v_i)`.

## (6) Greedy selection stops by dimension 2R

*Claim.* If Gram--Schmidt residuals `v_1, ..., v_m` of distinct columns
`w_(z_1), ..., w_(z_m)` all satisfy `||v_l||^2 > tau`, then `m <= max(2R - 1, 0)`.

*Gram determinant.* Let `G = (<w_(z_i), w_(z_l)>)`. Gram--Schmidt is a unit
lower triangular change of basis, so `det G = prod_l ||v_l||^2 > tau^m`.

*Principal minor.* `G = (P^T P)_(J,J) = (B^(2t))_(J,J)`, with
`J = {z_1, ..., z_m}`. `B^(2t)` is positive semidefinite with eigenvalues
`mu_i = lambda_(B,i)^(2t) in [0, 1]`. Its principal minors are nonnegative, so
`det G <= e_m(mu)`.

*Eigenvalue count.* Put `nu = (1 - gamma)^(2t)`. At most `R` of the `mu_i` are
`>= nu`, so for `m >= R`, `e_m(mu) <= binom(n, m) nu^(m - R) <= n^m nu^(m - R)`.
Also `nu <= exp(-2 gamma t) <= exp(-1.4 (40 + 7L))`, and
`tau^2/n^2 >= 2^(-80 - 14L) = exp(-2 ln 2 (40 + 7L))`. Since
`2 ln 2 < 1.4`, `nu <= tau^2/n^2`.

*Contradiction.*
- If `R >= 1` and `m >= 2R`: `tau^(2R) < n^(2R) nu^R <= tau^(2R)`.
- If `R = 0` and `m >= 1`: `tau < n nu <= tau^2/n < tau`.

*Consequences.*
- Suppose `R <= R*` and step 2 output "rank above `R*`". Then `2R*` residuals
  exceed `tau`, and so does one more. So `2R* + 1 <= max(2R - 1, 0)`, which forces
  `R >= R* + 1`, a contradiction. This proves item 2.
- By the same count, "rank above `R*`" forces `R > R*`. This proves item 1.
- At the ordinary stop, `m <= 2R*` and `||Q w_z||^2 <= tau` for every `z`.

## (7) YES instances are accepted at the ordinary stop

Let `S` have `|S| = s` and `Phi(S) <= eta`, and suppose the ordinary stop was
reached. The size of `R` plays no role here. Split `f = 1_S = f_hi + f_lo` at
`theta_hi`.

*Low part.* By (2),
`||f_lo||^2 <= s eta / (2 gamma/8) = 4 eta s/(400 eta) = s/100`.

*High part.*
- Write `f_hi = sum_phi c_phi phi` over orthonormal eigenvectors with
  `lambda_phi >= theta_hi > 0`, and put `p = sum_phi c_phi lambda_phi^(-t) phi`.
- Then `P p = f_hi` and `||p|| <= theta_hi^(-t) ||f_hi|| <= theta_hi^(-t) sqrt(s)`.
- By Cauchy--Schwarz, `sum_z |p(z)| <= sqrt(n) ||p||`. Since `f_hi = sum_z p(z) w_z`,
  `||Q f_hi|| <= sum_z |p(z)| ||Q w_z|| <= sqrt(n) theta_hi^(-t) sqrt(tau) sqrt(s)`.

*Numbers.*
- `-ln(1 - y) <= 2y` for `y <= 1/2` gives `theta_hi^(-t) <= exp(gamma t/4)`.
- `gamma t/4 <= 0.175 (40 + 7L) + gamma/4 <= 0.175 (40 + 7L) + 0.125`.
- So `log2(sqrt(n) theta_hi^(-t) sqrt(tau)) <= L/2 + log2(e) (0.175 (40 + 7L) + 0.125) - 20 - 3L`
  `<= -0.7327 L - 9.72 < log2(1/100)`.
- Hence `||Q f_hi|| <= sqrt(s)/100`.

*Projection.*
- `||f - (I - Q) f|| = ||Q f|| <= ||f_lo|| + ||Q f_hi|| <= sqrt(s)/10 + sqrt(s)/100`.
- Write `(I - Q) f = sum_l c_l psi_l` with `c_l = <f, psi_l>/||psi_l||^2`. Then
  `|c_l| <= ||f||/||psi_l|| <= 1`, so some `d_l in Lev` has `|c_l - d_l| <= h/2`.
- Orthogonality gives
  `||(I - Q) f - g||^2 = sum_l (c_l - d_l)^2 ||psi_l||^2 <= m (h^2/4) 4s <= 0.09^2 s`.
- So `||g - f|| <= (0.09 + 0.01 + 0.1) sqrt(s) = 0.2 sqrt(s)`.
- If `m = 0`, then `g = 0` and this reads `sqrt(s) <= 0.2 sqrt(s)`, which is
  impossible. So a YES instance at the ordinary stop has `m >= 1`.

*Value.*
- By (3), `|T xor S| <= 0.16 s`, so `|T| in [0.84 s, 1.16 s]`.
- `e(T) >= (1 - eta) d s - 0.32 d s`, so `1 - Phi(T) >= (0.68 - eta)/1.16`.
- If `|T| <= s`, then `kappa(|T|) >= 0.84`. If `|T| > s`, then
  `kappa(|T|) >= (s - 1)/(1.16 s - 1)`. This is increasing in `s` and equals
  `99/115 > 0.86` at `s = 100`.
- So `rho(T) >= 0.84 (0.68 - 1/800)/1.16 > 0.4915 > eta`, and the output is
  ACCEPT. This proves item 3.

## (8) Accepting is sound

If ACCEPT is output, some `T` has `rho(T) > eta`. By (4), some `s`-set `T'` has
`1 - Phi(T') > eta`, that is `Phi(T') < 1 - eta`, so the instance is not NO.
For `s < 100`, the exhaustive search is exact. This proves item 4 with no rank
hypothesis.

## (9) Bit complexity

- *Integer walk power.* `Y = (dI + M)^t = (2d)^t P` is an integer matrix with
  nonnegative entries and row sums `(2d)^t`.
- *Rescaling.* Run step 2 on the columns `y_z` of `Y`, with `tau` replaced by
  `(2d)^(2t) tau`, and step 3 with `s` replaced by `(2d)^(2t) s`. Residuals scale
  by `(2d)^t` and squared norms by `(2d)^(2t)`, so the run and its decisions are
  unchanged, and `psi_l` is recovered exactly.
- *Size of K.* `K = n (2d)^(2t)` bounds every `<y_z, y_z>`, and
  `log2 K = O(log n + t log(2d)) = poly(Z, 1/eta)` since `t = O(L/eta)`.
- *Residual entries.* Let `v` be the residual of `y` against independent
  integer vectors `y_1, ..., y_i` with Gram determinant `D_i >= 1`. Cramer's rule
  makes `D_i v` integral. We have `v(z)^2 <= <y, y> <= K`, and by (6)
  `D_i = prod_l ||v_l||^2 <= K^i`. So every entry is a fraction with at most
  `(i + 1) log2 K` bits in numerator and denominator.
- *Coefficients.* `<y, v_l>/<v_l, v_l>` has `<v_l, v_l> = D_l/D_(l-1)`, and
  `D_(l-1) <y, v_l>` is an integer of absolute value `<= n K^(l+1)`.
- *Grid step.* The integers `e_l`, the grid `h`, each `g`, each `T`, `e(T)` and
  the comparison `rho(T) > eta` all have polynomially many bits.
- *Time.* Step 2 runs at most `2R* + 1 <= 2n + 1` rounds of `n` residuals. Step 5
  evaluates `|Lev|^m <= (2/h + 2)^(2R*) <= (4 sqrt(2R* + 1)/0.09 + 2)^(2R*)` grid
  points. The total is `poly(Z, 1/eta) exp(O(R* log(R* + 1)))`. This proves
  Theorem 1.

## (10) Two-sided class kill

Let `Red` be as in Theorem 2, and fix a cutoff `R*(Z)`. The decider `D_YES` or
`D_NO` runs Theorem 1 on `Red(phi)`:

- on "rank above `R*`", `D_YES` answers NO and `D_NO` answers YES;
- otherwise both answer YES iff ACCEPT.

*Correctness of `D_YES`* (every YES output has `R <= R*`).
- A satisfiable `phi` never gets "rank above", by item 2, and gets ACCEPT by item 3.
- An unsatisfiable `phi` gives a NO instance. "Rank above" answers NO, and ACCEPT
  is impossible by item 4.

*Correctness of `D_NO`* (every NO output has `R <= R*`).
- An unsatisfiable `phi` never gets "rank above", by item 2, and never gets
  ACCEPT, by item 4. So it gets REJECT, answered NO.
- A satisfiable `phi` gets either "rank above", answered YES, or the ordinary
  stop, where item 3 gives ACCEPT.

*Time.* Both run in `poly(Z) exp(O(R* log(R* + 1)))`, plus `n^99 poly(Z)`.
- `R* = c log Z / log log Z` gives `poly(Z) Z^(O(c))`, so `P = NP`.
- `R* = (log Z)^c` gives `exp(O((log Z)^c log log Z))`.

*ETH.* ETH says that for some `delta0 > 0`, 3SAT on `n` variables has no
`2^(delta0 n)`-time algorithm. Let `Z <= n^A` and `alpha < 1/A`.

- Suppose only finitely many YES outputs have `R > Z^alpha`. Run `D_YES` with
  `R* = Z^alpha <= n^(A alpha)`, and answer the finitely many exceptional formulas
  from a table. The time is `exp(O(n^(A alpha) log n)) = 2^(o(n))`, contradicting
  ETH.
- The NO side is the same argument with `D_NO`.

This proves Theorem 2.

## (11) Certificate collapse

- *Verifier.* Given `(M, s)` and a candidate certificate
  `(c, (q_j), (a_u), b)` of bit length `beta`, check `c < 1 - eta` and expand both
  sides of the identity. The right side has at most `beta^2 + n beta + beta`
  monomial products before collection, so the check takes `poly(beta, Z)` time.
- *Soundness.* At `x = 1_S` with `|S| = s`, every `x_u^2 - x_u` and
  `sum x_u - s` vanishes, and `sum q_j^2 >= 0`. So `c d s - e(S) >= 0`, that is
  `1 - Phi(S) <= c < 1 - eta`, and `Phi(S) > eta`. A YES instance has no
  certificate.
- *Collapse.* Suppose every NO output of `Red` has a certificate of bit length
  `<= beta(Z)`. Then `phi` is unsatisfiable iff `Red(phi)` has a certificate of
  that length:
  - if `phi` is unsatisfiable, the output is NO and a certificate exists;
  - if `phi` is satisfiable, the output is YES and no certificate exists.

  So `UNSAT in NTIME(poly(beta(Z), Z))`. A polynomial `beta` gives `NP = coNP`,
  and a quasi-polynomial one gives `coNP <= NQP`.
- *Example identity at `c = 1`.* The polynomial identity
  `d s - e(x) = (1/2) sum_(u,v) M(u,v)(x_u - x_v)^2 - d sum_u (x_u^2 - x_u) - d (sum_u x_u - s)`
  holds exactly. The replay script checks it with `Fraction` coefficients. This is
  the trivial bound, and a NO certificate needs `c < 1 - eta`.

This proves Theorem 3.

## (12) The abelian Cayley survivor

`Cay(F_2^N, {e_1, ..., e_N})` has `A` with eigenvectors the characters `chi_w`
and eigenvalues `1 - 2|w|/N`. So `rank_(1-800 eta)(A) = sum_(k <= 400 eta N) binom(N, k)`.
For fixed `eta` this is `2^(Omega(N))`, polynomial in `n = 2^N`, far above every
polylogarithm. Threshold rank therefore does not kill reductions with abelian
Cayley outputs, and whether (G-cert) does is left open.
