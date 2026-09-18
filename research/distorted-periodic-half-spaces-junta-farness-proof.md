---
rg: 2
id: distorted-periodic-half-spaces-junta-farness-proof
kind: route
title: The Gaussian measure mod 1 is uniform within 6e-9, so a distorted periodic half-space has bounded level density and its test rejections are Rice crossing integrals of honest size, while every Fourier term of its correlation with a bounded junta factors over coordinates into characters of modulus at most lambda_K(a) < 1
target: distorted-periodic-half-spaces-defeat-real-code-junta-decoding
requires: []
artifacts:
  - experiments/real-code-distortion-2026-09-17/check_distorted_real_code.py
---

Notation is as in the target claim: `phi = phi_a`, `g(x) = sum_i sigma_i phi(x_i)`,
`nu = 6e-9`, `mu = e^(-2 pi^2)`, `gamma` the standard Gaussian density, and
`s(z) = interval(z)`, a 2-periodic `+-1` square wave. Only the Khot--Moshkovitz
test definitions (quoted in the target) are used, not their lemmas.

## (0) Level density

**(0a)** By Poisson summation, `sum_(j in Z) gamma(u + j) = sum_(m in Z) e^(-2 pi^2 m^2) e^(2 pi i m u)`.
This lies in `[1 - 2 mu - 2 mu^4, 1 + 2 mu + 2 mu^4] <= [1 - nu, 1 + nu]`. For the density `p_v` of `N(0, v^2)` with
`v >= 1`, `sum_j p_v(u + j) = sum_m e^(-2 pi^2 m^2 v^2) e^(2 pi i m u)`, and the same bound holds.
(Replay part B.)

**(0b) Lemma.** Let `X in R^T` have density at most `M gamma_T`, with `T` nonempty.
Let `c` be a real constant and `h(x) = c + sum_(i in T) sigma_i phi(x_i)`. Then for every
interval `I` with `|I| <= 1`,
`P[h(X) mod 1 in I] <= M |I| (1 + nu)/(1 - a)`.

*Proof.* Fix `i in T`. By the density domination, it suffices to take `X ~ gamma_T` and
multiply by `M`. Condition on the other coordinates. `phi` is an increasing
`C^1` bijection with `phi' >= 1 - a` and `phi^(-1)(v + j) = phi^(-1)(v) + j`. So
`sigma_i phi(X_i)` has density `gamma(phi^(-1)(+-v)) / phi'(phi^(-1)(+-v))`. Its
periodization at `v` is at most `(1/(1 - a)) sum_j gamma(u + j) <= (1 + nu)/(1 - a)`,
with `u = phi^(-1)(+-v)`. Adding an independent (conditioned) constant is a
translation, which preserves the sup of a periodized density. Integrate over the
other coordinates. QED.

## (1) Folding

`phi(t + 1) = phi(t) + 1`, so `g(x + e_i) = g(x) +- 1`, and `s(z +- 1) = -s(z)` whenever
`z` is not an integer. `phi` is odd, so `g(-x) = -g(x)` and `s(-z) = -s(z)` for
`z not in Z`. The set `{g in Z}` is a null set, because `g` is a submersion
(`|partial_1 g| >= 1 - a`).

## (2) Crossing lemma

Let `x(theta)`, `theta in [0, theta_0]`, be a `C^1` random path in `R^n`, and put
`h(theta) = g(x(theta))`. Suppose that for every `theta`:

- (i) `E[ |h'(theta)| | x(theta) ] <= B(x_C(theta))`, where `x_C` is a sub-vector
  of coordinates (possibly empty) and `B` is measurable;
- (ii) conditional on `x_C(theta)`, the vector of coordinates not in `C` has density
  at most `M gamma`, and `n > |C|`.

Then `P[ s(g(x(0))) != s(g(x(theta_0))) ] <= theta_0 M (1 + nu)/(1 - a) * sup_theta E B(x_C(theta))`.

*Proof.* For `u in [0, 1)` let `N_u` count the `theta` with `h(theta) in Z + u`. Let
`E_u` be the event `s(h(0) - u) != s(h(theta_0) - u)`. By continuity of `h`,
`E_u <= {N_u >= 1}`. Fix `eta in (0, 1)` and `rho = 1_[0, eta] / eta`. By the Banach
indicatrix formula (area formula in one variable),
`int_0^1 rho(u) N_u du = int_0^(theta_0) rho(h(theta) mod 1) |h'(theta)| d theta`.
Take expectations and condition on `x(theta)`. By (i),
`E[rho(h mod 1) |h'|] <= E[rho(h mod 1) B(x_C)]`. Now condition further on `x_C`: by
(ii) and (0b), `E[rho(h mod 1) | x_C] <= M (1 + nu)/(1 - a)`. Therefore
```text
(1/eta) int_0^eta P(E_u) du <= theta_0 M (1 + nu)/(1 - a) sup_theta E B(x_C(theta)).
```
Almost surely `h(0)` and `h(theta_0)` are not integers (0b), and then
`1_(E_0) <= liminf_(u -> 0+) 1_(E_u)`. By Fatou,
`P(E_0) <= liminf_(eta -> 0) (1/eta) int_0^eta P(E_u) du`. QED.

## (3) Low boundary test on `K`

Put `theta_0 = arccos(1 - alpha)`, so that `cos theta_0 = 1 - alpha` and
`sin theta_0 = sqrt(2 alpha - alpha^2)`. Let `x(theta)` agree with `x` off `K` and
equal `cos theta x_K + sin theta w_K` on `K`. Then `x(0) = x` and `x(theta_0) = y`.
For each `theta`, `x(theta) ~ gamma_n`. The derivative `x'(theta)` vanishes off `K` and
equals `-sin theta x_K + cos theta w_K` on `K`, a standard Gaussian vector independent
of `x(theta)`. Hence
`h'(theta) = sum_(i in K) sigma_i phi'(x_i(theta)) x_i'(theta)` is, conditional on
`x(theta)`, centred Gaussian with standard deviation
`(sum_(i in K) phi'(x_i)^2)^(1/2) <= (1 + a) sqrt|K|`. So (i) holds with
`C = emptyset` and `B = sqrt(2/pi)(1 + a) sqrt|K|`, and (ii) holds with `M = 1`. The
crossing lemma gives item 2.

Replay part A checks `arccos(1 - alpha) <= (pi/2) sqrt(alpha)` on a grid. A proof:
with `alpha = 1 - cos theta = 2 sin^2(theta/2)` the inequality reads
`theta <= (pi/sqrt 2) sin(theta/2)` for `theta in [0, pi/2]`. It holds by concavity of
`sin` on `[0, pi/4]`, which gives `sin(theta/2) >= (theta/2) sin(pi/4)/(pi/4) = sqrt2 theta/pi`.
So the bound is `<= sqrt(pi/2)(1 + a)(1 + nu)/(1 - a) sqrt(alpha |K|)`.

*Honest lower bound (`a = 0`, `K = [n]`).* Put `D = <sigma, y - x>` and
`g_0 = <sigma, x + y>/2`. They are jointly Gaussian with
`Cov(x + y, y - x) = Var y - Var x = 0`, so they are independent. Also
`Var D = n(2 - 2(1 - alpha)) = 2 alpha n` and `Var g_0 = n(1 - alpha/2) >= n/2`. The test
rejects iff an odd number of integers lies between `g_0 - D/2` and `g_0 + D/2`. When
`|D| < 1` this happens iff exactly one integer lies there. Conditional on `D`, that has
probability equal to the integral of the periodized density of `g_0` over a
length-`|D|` interval. By (0a) that density is at least
`1 - 2 sum_(m >= 1) e^(-pi^2 m^2 n) >= 1 - 3 e^(-pi^2 n)`. Hence
`P[reject] >= (1 - 3e^(-pi^2 n)) E[|D| 1_(|D| < 1)] >= (1 - 3e^(-pi^2 n)) (E|D| - E D^2)`
`= (1 - 3e^(-pi^2 n)) (2 sqrt(alpha n/pi) - 2 alpha n)`. The ratio of the item-2 upper
bound to this is `(pi/(2 sqrt 2)) (1 + a)(1 + nu)/(1 - a) (1 + O(sqrt(alpha n) + e^(-pi^2 n)))`,
and `pi/(2 sqrt 2) = 1.1107...`.

## (4) Constraint test

Write `x = x_perp + t v_C` with `t = <x, v_C>`, and let `z ~ N(0, 1)` be independent.
The test's `y` equals `x_perp + t' v_C` with `t' = cos theta_0 t + sin theta_0 z`, where
`cos theta_0 = 1 - beta^2/2` (KM footnote 4). Put `x(theta) = x_perp + (cos theta t + sin theta z) v_C`.
Then `x(theta) ~ gamma_n` and `x'(theta) = (-sin theta t + cos theta z) v_C`, whose scalar
factor is `N(0, 1)` and independent of `x(theta)`. So
`E[|h'(theta)| | x(theta)] = sqrt(2/pi) |sum_(i in C) sigma_i (v_C)_i phi'(x_i(theta))| =: B(x_C(theta))`.
The coordinates outside `C` are independent of `x_C` and standard Gaussian, so (ii)
holds with `M = 1` when `n > k`. Next, `phi'(t) = 1 + a cos(2 pi t)` and
`E cos(2 pi X) = e^(-2 pi^2) = mu`. So
```text
E B <= sqrt(2/pi) ( |<sigma, v_C>| + a E|sum_i sigma_i (v_C)_i cos(2 pi x_i)| )
    <= sqrt(2/pi) ( |<sigma, v_C>| + a ( mu sum_i |(v_C)_i| + (sum_i (v_C)_i^2)^(1/2) ) )
     = sqrt(2/pi) ( |<sigma, v_C>| + a (mu sqrt k + 1) ).
```
The second line splits the sum into its mean and a centred part, and bounds the
centred part by its standard deviation. The crossing lemma gives item 3.
For KM's Lasserre local distributions (KM Lemma 5.1, equation (10)),
`<sigma, v_C> = -1/sqrt k` with probability `k/(k+1)` and `sqrt k` with probability
`1/(k+1)`. So `E|<sigma, v_C>| <= 2/sqrt k`, and with `a <= 1/sqrt k` and
`arccos(1 - beta^2/2) <= (pi/2) beta` the average rejection is
`<= sqrt(pi/2) (1 + nu)/(1 - a) (3 + mu sqrt k) beta/sqrt k = O(beta/sqrt k)`.

## (5) Consistency test

In KM's test (Section 6), `f_S(x, x', y_S)` and `f_R(x, x', y_R)` share the large
coordinates `x ~ D_Ibar^U` and the small coordinates `x'`. They differ only in
`y_S, y_R ~ D_I^m`, all of absolute value at most `s`, where `I = [-s, s]` has
Gaussian measure `delta`. The distorted strategy uses
`f_S = s(A + B_S)` and `f_R = s(A + B_R)`. Here `A` is the sum over `U` and
`U n U'` with the shared assignment `pi`, and `B_S = sum_l sigma^(S)_l phi(y^S_l)`,
and similarly for `B_R`. A rejection needs an integer between `A + B_S` and
`A + B_R`. Condition on `x', y_S, y_R`. The coordinates of `x` are independent with
density `gamma 1_Ibar/(1 - delta) <= gamma/(1 - delta)`, and `U` is nonempty (with
probability `1 - delta^n`). So by (0b), with `M = 1/(1 - delta)`,
`P[reject | x', y] <= M (1 + nu)/(1 - a) |B_S - B_R|` (for `|B_S - B_R| <= 1`; otherwise
the bound exceeds 1 anyway). The `2m` summands of `B_S - B_R` are independent,
symmetric (`phi` odd, `D_I` symmetric) and bounded by `(1 + a) s`. So
`E|B_S - B_R| <= (2m)^(1/2) (1 + a) s <= 2 (1 + a) s sqrt m`. This is item 4. KM take
`s ~ sqrt(2 pi) delta/2` and `m = n - |U|`, which has mean `delta n`. So the rate is
`O(delta sqrt(delta n))`, matching KM Lemma 6.1.

## (6) Surface area

`g` is smooth with `|grad g| in [(1 - a) sqrt n, (1 + a) sqrt n]`. Put
`A(u) = sum_(j in Z) int_({g = j + u}) gamma dH^(n-1)`. By the coarea formula, for
`rho = 1_[0,eta]/eta`,
`int_0^1 rho(u) A(u) du = E[ rho(g mod 1) |grad g| ] <= (1 + a) sqrt n (1 + nu)/(1 - a)`,
using (0b). `A` is continuous in `u`. The flow of `V = grad g / |grad g|^2` carries
`{g = c}` onto `{g = c + t}`. `|V| <= 1/((1 - a) sqrt n)`, and `DV` is bounded because
`|phi''| <= 2 pi a`. So the Jacobians are `e^(O(|t|))` and
`gamma(psi_t y) <= gamma(y) e^(O(|t| |y| + t^2))`, and dominated convergence applies
(the level sets have Gaussian-integrable area density). Letting `eta -> 0` gives
`A(0) <= (1 + a)(1 + nu)/(1 - a) sqrt n`. For `a = 0`, `A(0) = sqrt n sum_j p_(sqrt n)(j)`
with `p_v` the `N(0, v^2)` density, which equals
`sqrt n sum_m e^(-2 pi^2 m^2 n) >= sqrt n`, since every term is positive. This is item 5. Item 5 is not used in items 6--7.

## (7) Farness from bounded juntas (item 6)

Fix `a in (0, 1)`, `l`, `eta`. Let `T` be the free coordinates, with `|T| >= n/2`,
and fix the other coordinates to constants. Then `g = c_0 + sum_(i in T) sigma_i phi(x_i)`
and `<tau_j, x> = c_j + <tau_(j,T), x_T>`. If `tau_(j,T) = 0`, the `j`-th junta input
is a constant; substitute it into `G`. So assume every `tau_(j,T)` is a nonzero
integer vector, and hence `<tau_(j,T), x_T> ~ N(0, v^2)` with `v >= 1`.

**(7a) Fejer truncation.** `s(z) = sum_(k odd) c_k e^(i pi k z)` with
`c_k = 2/(i pi k)`. Let `F_K s = sum_(|k| <= K) (1 - |k|/(K+1)) c_k e^(i pi k z)`, the
Fejer mean. It is a convolution of `s` with a probability kernel, so `|F_K s| <= 1`.
By Parseval on `R/2Z` with normalized measure,
```text
|| s - F_K s ||_2^2 = sum_(|k| <= K) |c_k|^2 k^2/(K+1)^2 + sum_(|k| > K) |c_k|^2 <= 8/(pi^2 (K+1)) + 8/(pi^2 K) <= 2/K.
```
Let `Z` be a real random variable with `P[Z mod 1 in I] <= D |I|` for `|I| <= 1`. The
law of `Z mod 2` then has density at most `2D` with respect to the normalized measure,
so `E|s(Z) - F_K s(Z)| <= (2D)^(1/2) (2/K)^(1/2)`. By (0b) and (0a), `D = (1 + nu)/(1 - a)`
works for `g` and every `<tau_j, x>`.

**(7b) Telescoping.** Write `G(u) = sum_(A <= [l]) hat G(A) prod_(j in A) u_j`, the
multilinear extension, with `|hat G(A)| <= 1`. On `[-1, 1]^l` it is an average of vertex
values, so `|G| <= 1`, and it is 1-Lipschitz in each coordinate separately. Replace
`s` by `F_K s` in the `l + 1` factors one at a time. The error in
`E[s(g) G(s(<tau_1,x>), ...)]` is at most `(l + 1) 2 ((1 + nu)/((1 - a) K))^(1/2)`. Choose
`K` odd with this `<= eta/2`.

**(7c) Product formula.** Expand the truncated correlation. It is a sum over
`A <= [l]` and odd `k_0, k_j` with `|k| <= K`, with coefficient modulus at most
`|hat G(A)| prod |c_k|`, of
```text
E exp(i pi (k_0 g + sum_(j in A) k_j <tau_j, x>)) = (phase) * prod_(i in T) psi(k_0 sigma_i, omega_i),
omega_i = sum_(j in A) k_j tau_(j,i) in Z,     psi(kappa, w) = E exp(i pi (kappa phi(X) + w X)).
```
The product uses independence of the coordinates of `x_T`. Each factor has `kappa` odd with
`|kappa| <= K`, so its modulus is at most `lambda_K(a)`. With
`L_K = sum_(|k| <= K, odd) 2/(pi |k|) <= 2 + log K`,
```text
| truncated correlation | <= 2^l L_K^(l+1) lambda_K(a)^(n/2).
```

**(7d) `lambda_K(a) < 1`.** Put `Theta(t) = pi(kappa phi(t) + w t)`.

- *Large `|w|`.* `|kappa phi'| <= K(1 + a)`, so for `|w| >= 2K(1 + a)` we have
  `|Theta'| >= pi |w|/2`. Integrate by parts, using `e^(i Theta) = (e^(i Theta))'/(i Theta')`
  and the decay of `gamma`:
  `|psi| <= int |gamma'|/|Theta'| + int gamma |Theta''|/Theta'^2`. Here
  `int |gamma'| = sqrt(2/pi)` and `|Theta''| = pi |kappa phi''| <= 2 pi^2 K a`. So
  `|psi| <= 2 sqrt(2/pi)/(pi |w|) + 8 K a/w^2 <= 1/2` once `|w| >= W_K := max(2K(1+a), 4, 6 sqrt(K))`.
- *Finitely many remaining pairs.* For `|w| < W_K`, `|psi(kappa, w)| <= int gamma = 1`,
  with equality iff `e^(i Theta)` is a.e. constant, since `gamma > 0` everywhere. As
  `Theta` is continuous, that makes `Theta` constant mod `2 pi` on `R`, hence constant.
  Then `kappa phi' + w = kappa(1 + a cos 2 pi t) + w = 0` for all `t`, which is
  impossible for `kappa != 0` and `a > 0`.

So `lambda_K(a) = max(1/2, max over the finite set) < 1`. (Replay part C:
`lambda_7(0.1) = 0.99937`, `lambda_7(0.8) = 0.9604`, attained at `(kappa, w) = (1, -1)`.
At `a = 0`, `|psi(1, -1)| = 1`, which is the honest code correlating with itself.)

Choose `n_0` with `2^l L_K^(l+1) lambda_K(a)^(n_0/2) <= eta/2`. Then for `n >= n_0` the
correlation is at most `eta`, uniformly in `sigma`, `G`, `tau` and the fixed
coordinates. Since `f` and `J` are `+-1`-valued,
`Pr[f = J] = (1 + E fJ)/2 <= (1 + eta)/2`.

## (8) Not list decodable (item 7)

A real code junta `J_S` "depending on at most l real code functions" is
`G(s(<sigma_(S,1), x>), ..., s(<sigma_(S,l), x>))` with `sigma_(S,j) in {+-1}^n`, which are
nonzero integer vectors, and some `G : {+-1}^l -> {+-1}`. By (7), with `eta < 1/2` and
`n >= n_0(a, l, eta)`, every `S` has `Pr[f_S = J_S] <= (1 + eta)/2 < 3/4 < 1 - gamma`
for every such `J_S`. So the fraction of sets `S` that admit a decoding is 0, which
is less than `1 - gamma`. The test bounds come from (3)--(5), and folding from (1). QED.

## Scope

- The quantifiers are "for fixed `a`, then `n` large", which is KM's regime: `n`
  grows with `N`, and `k`, `l`, `gamma` are constants. When `a <= 1/sqrt k` is used for
  the constraint test, `a` is still a constant.
- The Fourier contraction behaves numerically like `1 - a^2/16`, so the argument
  says nothing when `a -> 0` faster than `n^(-1/2)`.
- Nothing here bears on (P-a), (P-b), (P-c), or on reparametrization-invariant
  soundness (P-c'), (P-d').
