# The two-point function and the Fourier algebra (2026-09-17)

Author: swarm-0917-w7-w7-bs-pull (transplanter, operator algebras).

## 0. Setting and notation

- `Gamma` is finitely generated and nonamenable. `S` is a finite symmetric
  generating set, `G = Cay(Gamma,S)`, and `mu` is uniform on `S`.
  `rho = ||lambda(mu)|| < 1`, where `lambda` is the left regular
  representation on `l^2(Gamma)`.
- `tau_p(x) = P_p(e <-> x)` for Bernoulli bond percolation. `C(v)` is the
  cluster of `v` and `theta(p) = P_p(|C(e)| = infinity)`.
- `a_n(p) = sum_x mu^(*n)(x) tau_p(x)`, and
  `lambda(p) = lim a_n(p)^(1/n)` as in
  `research/artifacts/fpbs/docs/lq-two-point-walk-rate-2026-09-17.md`
  (Lemma 2.1 gives existence, Lemma 2.2 gives `lambda(p) >= rho`).
- `B(Gamma)` is the Fourier–Stieltjes algebra and `A(Gamma)` the Fourier
  algebra (Eymard). `A(Gamma)^+` denotes the positive definite (PD)
  functions of the form `x -> <lambda(x) eta, eta>` with `eta` in
  `l^2(Gamma)`. For PD `phi`, `||phi||_B = phi(e)`.
- For `f` in `C_c(Gamma)` and a set `C`, put `f(C) = sum_(x in C) f(x)`.

## 1. The cluster form

For PD `phi` define on `C_c(Gamma)` the form
`q_phi(f) = sum_(x,y) conj(f(x)) f(y) phi(x^(-1) y)`.

**Lemma 1.1 (cluster form).**
`q_(tau_p)(f) = E_p sum_C |f(C)|^2`, where the sum runs over all clusters.
In particular `tau_p` is PD. The same identity holds for the finite and
infinite parts:

- `tau^fin_p(x) = P_p(e <-> x, |C(e)| < infinity)` has
  `q(f) = E sum_(C finite) |f(C)|^2`;
- `tau^inf_p(x) = P_p(e <-> x, |C(e)| = infinity)` has
  `q(f) = E sum_(C infinite) |f(C)|^2`.

Both are PD and `tau_p = tau^fin_p + tau^inf_p`.

*Proof.* Expand `|f(C)|^2` and use `1{x <-> y} = sum_C 1{x in C, y in C}`.
Then `P(x <-> y) = tau_p(x^(-1) y)` by invariance. The sum over `C` is finite
because `f` has finite support. Restricting to finite or infinite clusters is
the same computation. QED.

## 2. The closability criterion

**Theorem 2.1.** Let `phi` be PD on `Gamma` and real, with `phi(e) = 1`. The
following are equivalent.

- (a) The form `q_phi` on `C_c(Gamma)` is closable in `l^2(Gamma)`.
- (b) `phi` is in `A(Gamma)^+`: there is `eta` in `l^2(Gamma)` with
  `phi(x) = <lambda(x) eta, eta>` for all `x`, and `||eta||^2 = 1`.

*Proof of (b) => (a).* Let `eta~(x) = conj(eta(x^(-1)))`. Define `R` on
`C_c(Gamma)` by `R f = f * eta`, where
`(f * eta)(z) = sum_y f(y) eta(y^(-1) z) = (sum_y f(y) lambda(y) eta)(z)`.
Then `R f` is in `l^2` and

`||R f||^2 = sum_(x,y) conj(f(x)) f(y) <lambda(y) eta, lambda(x) eta>
           = sum_(x,y) conj(f(x)) f(y) phi(x^(-1) y) = q_phi(f)`.

For `f, h` in `C_c` we have `<R f, h> = <f, h * eta~>`, and `h * eta~` is in
`l^2`. So `R^*` is defined on the dense set `C_c`, hence `R` is closable.

Now let `f_k -> 0` in `l^2` with `q_phi(f_k - f_j) -> 0`. Then `R f_k` is
Cauchy, so `R f_k -> v`. Closability of `R` gives `v = 0`, so
`q_phi(f_k) = ||R f_k||^2 -> 0`. That is exactly closability of the form. QED.

*Proof of (a) => (b).*

1. Let `qbar` be the closure, with domain `D`. The form is densely defined,
   closed and nonnegative. By the first and second representation theorems
   (Kato, *Perturbation Theory for Linear Operators*, Ch. VI Sec. 2), there is a positive self-adjoint `T` with
   `D = dom(T^(1/2))` and `qbar(f,h) = <T^(1/2) f, T^(1/2) h>`.
2. For `g` in `Gamma`, `lambda(g)` preserves `C_c` and
   `q_phi(lambda(g) f) = q_phi(f)`, by the substitution
   `x -> g x, y -> g y`. Hence `lambda(g) D = D` and `qbar` is
   `lambda(g)`-invariant.
3. By uniqueness in the representation theorem,
   `lambda(g)^* T lambda(g) = T`. So `T` commutes with `lambda(Gamma)`, and so
   does every bounded Borel function of `T`. Therefore `T^(1/2)` is affiliated
   with `lambda(Gamma)' = R(Gamma)`, the right group von Neumann algebra, and
   `T^(1/2) lambda(g) = lambda(g) T^(1/2)` on `D`.
4. Put `eta = T^(1/2) delta_e`, which is in `l^2` because `delta_e` is in
   `C_c`, a subset of `D`. Then
   `phi(g) = q_phi(delta_e, delta_g)
           = <T^(1/2) delta_e, T^(1/2) lambda(g) delta_e>
           = <eta, lambda(g) eta>`.
   Since `phi` is real and symmetric, this equals `<lambda(g) eta, eta>`.
   Finally `||eta||^2 = phi(e) = 1`. QED.

**Corollary 2.2 (l^2 implies A).** If `phi` is PD and in `l^2(Gamma)`, then
`phi` is in `A(Gamma)^+`.

*Proof.* The operator `f -> f * phi` on `C_c` maps into `l^2`, is symmetric
because `phi(x^(-1)) = conj(phi(x))`, and is nonnegative with quadratic form
`q_phi`. The form of a nonnegative symmetric operator is closable
(Friedrichs extension; Reed–Simon II, Theorem X.23), so Theorem 2.1 applies. QED.

This recovers Godement's classical theorem that a PD `l^2` function has the
form `eta * eta~`.

**Corollary 2.3 (Bernoulli).** `tau_p` is in `A(Gamma)^+` if and only if the
cluster form `f -> E_p sum_C |f(C)|^2` is closable in `l^2(Gamma)`.

## 3. Consequences of membership

**Theorem 3.1.** Suppose `tau_p` is in `A(Gamma)^+`, with vector `eta`. Then:

1. `a_n(p) <= rho^n` for every `n >= 0`, with constant 1. Hence
   `lambda(p) = rho`.
2. `tau_p` is in `c_0(Gamma)`.
3. If `p > p_c`, then `p` is in the nonuniqueness phase, so `p_c < p_u`.

*Proof.*

1. `a_n(p) = sum_x mu^(*n)(x) <lambda(x) eta, eta> = <lambda(mu)^n eta, eta>`,
   which is at most `||lambda(mu)||^n ||eta||^2 = rho^n`. With Lemma 2.2 of the
   l^q artifact (`lambda >= rho`), this gives `lambda(p) = rho`.
2. Choose `eta'` finitely supported with `||eta - eta'|| < eps`. Then
   `<lambda(x) eta', eta'> = 0` outside a finite set, and
   `|<lambda(x) eta, eta> - <lambda(x) eta', eta'>| <= 2 eps + eps^2`.
3. Suppose `p > p_c` and there is a unique infinite cluster at `p`. By Harris–FKG,
   `tau_p(x) >= P(e <-> infinity, x <-> infinity) >= theta(p)^2 > 0` for every
   `x`. This contradicts 2. So there are infinitely many infinite clusters at
   `p` (Newman–Schulman), and `p <= p_u` by monotonicity of uniqueness
   (Häggström–Peres 1999; Schonmann 1999). Since `p_c < p`, we get
   `p_c < p_u`. QED.

## 4. The finite-cluster part is always in A, and the distance

**Proposition 4.1.** For every `p`, `tau^fin_p` is in `A(Gamma)^+`. Consequently:

- `tau_p` is in `A(Gamma)` if and only if `tau^inf_p` is;
- `dist_B(tau_p, A(Gamma)) <= theta(p)`.

*Proof.*

1. Let `phi_R(x) = P_p(e <-> x, |C(e)| <= R)`. By Lemma 1.1 restricted to
   clusters of size at most `R`, `phi_R` is PD.
2. It is supported in the ball of radius `R`, so it is in `l^2`, and
   Corollary 2.2 puts it in `A(Gamma)^+`.
3. `tau^fin_p - phi_R` is PD by the same lemma, applied to clusters with
   `R < |C| < infinity`. So
   `||tau^fin_p - phi_R||_B = P_p(R < |C(e)| < infinity)`, which tends to 0.
4. `A(Gamma)` is norm-closed in `B(Gamma)` (Eymard 1964, "L'algebre de Fourier
   d'un groupe localement compact": `A(G)` is a closed ideal of `B(G)`). So
   `tau^fin_p` is in `A(Gamma)`.
5. The distance bound is `||tau^inf_p||_B = tau^inf_p(e) = theta(p)`. QED.

This is the Fourier-algebra form of the weak containment in
`fpbs-all-parameter-finite-cluster-spectrum`, and it is strictly stronger:
membership in `A` rather than weak containment in `lambda`.

**Corollary 4.2.** `theta` is right-continuous and `theta(p_c) = 0`
(`fpbs-critical-no-infinite-cluster`). Hence
`dist_B(tau_p, A(Gamma)) -> 0` as `p` decreases to `p_c`.

## 5. Thresholds, the hole [A], and calibrations

Let `p_A = sup{p : tau_s is in A(Gamma) for every s <= p}`.

**Proposition 5.1.**
`p_c <= p_(2->2) <= p_2 <= p_A`, and `p_A <= p_u`.

*Proof.* For `p < p_2` we have `tau_p` in `l^2`, so Corollary 2.2 applies;
this gives `p_2 <= p_A`. The first two inequalities are Lemma 4.1 of the l^q
artifact. For `p_A <= p_u`: at any `p > p_u` there is uniqueness and
`theta(p) > 0`, so `tau_p >= theta^2` is not in `c_0`. QED.

**The hole [A].** There are `p_k` decreasing to `p_c` with `tau_(p_k)` in
`A(Gamma)`. Equivalently, the infinite-cluster form
`f -> E_(p_k) sum_(C infinite) |f(C)|^2` is closable in `l^2` for each `k`.
This is implied by `p_c < p_A`, which is in turn implied by `p_c < p_2`.

**Theorem 5.2 ([A] implies IS and BS).** Assume [A].

- By Theorem 3.1, `lambda(p_k) = rho`.
- `tau_p` is pointwise nondecreasing in `p`, so `lambda` is nondecreasing.
  With `lambda >= rho`, this gives `lambda = rho` on `(p_c, p_1]`.
- By `fpbs-integrated-pivotal-rate-identity`, the normalised integrated
  sensitivity equals `log(lambda(p)/rho)`, so (IS) holds.
- Independently, Theorem 3.1(3) at `p_1` gives `p_c < p_u`.

**Calibration 5.3 (trees).** On the `d`-regular tree, as the Cayley graph of
`(Z/2)^(*d)` or of `F_r` with `d = 2r`, we have `tau_p(x) = p^|x|` and
`p_c = 1/(d-1)`.

- `p_2 = (d-1)^(-1/2)`, so `p_A >= p_2`.
- For `p > p_2`, the walk rate of `p^|x|` is the spherical value
  `(1/p + (d-1)p)/d`, which exceeds `rho = 2 sqrt(d-1)/d`. This is Section 5 of
  the l^q artifact, and the free-group numerics of
  `fpbs-hp-thinning-two-point-exit`. So by Theorem 3.1(1), `tau_p` is not in
  `A` for `p > p_2`.
- Hence `p_A = p_2`, which lies strictly between `p_c` and `p_u = 1`.
- [A] holds on trees, and the Fourier threshold is not `p_u`: membership in
  `A` is strictly stronger than nonuniqueness.

**Calibration 5.4 (rate rho does not give A).** Let `H` be an infinite amenable
subgroup. Then `1_H` is PD, its GNS representation `l^2(Gamma/H)` is weakly
contained in `lambda`, and its walk rate is `rho`. But `1_H` is not in `c_0`,
so it is not in `A`. So [A] is strictly stronger, at kernel level, than the
rate statement it is used to prove. Its extra content is decay (`c_0`) plus
closability.

**Calibration 5.5 (A and l^q are incomparable).**

- `A(Gamma)^+` does not embed in any `l^q` with `q < infinity` when `Gamma`
  has an element `g` of infinite order.
  - Take `c_n = 1/log(n+e)`, which is even in `n`, convex, and decreases to 0.
    By the classical convexity theorem (Zygmund, *Trigonometric Series* I,
    Ch. V, Thm 1.5) it is the Fourier coefficient sequence of a nonnegative
    `F` in `L^1(T)`. So `c` is in `A(Z)^+`.
  - Extend it by zero from `<g>` to `Gamma`. With `eta` in `l^2(<g>)`, a
    subset of `l^2(Gamma)`, the coefficient `<lambda(x) eta, eta>` vanishes
    off `<g>`. So the extension is in `A(Gamma)^+`, and it is in no `l^q`.
  - Hence membership in `A` carries no summability exponent, and [A] gives no
    obvious route to [Q].
- Conversely, `l^q` with `q > 2` does not embed in `A`. The tree functions
  `p^|x|` with `p_2 < p < (d-1)^(-1/q)` are in `l^q` but not in `A`.
- So [A] and [Q] (`fpbs-two-point-lq-threshold-gap-universal`) are
  incomparable sufficient conditions for (IS), with the common strengthening
  `p_c < p_2`.

**Corollary 5.6 (the critical state is in A).** On every nonamenable Cayley
graph `tau_(p_c)` is in `A(Gamma)^+`. This follows from Proposition 4.1 and
`theta(p_c) = 0`. In particular `a_n(p_c) <= rho^n`, which recovers Schramm's
lemma with constant 1, and `tau_(p_c)` is in `c_0`.

## 6. Where the operator-algebra transplant dies

The invariant is the *singular mass*
`s(phi) = dist_B(phi, A(Gamma))`, which is zero exactly on `A`.

**Bernoulli facts.**

- `s(tau_(p_c)) = 0` (Corollary 5.6).
- `s(tau_p) <= theta(p)`, which tends to 0 as `p` decreases to `p_c`
  (Corollary 4.2).
- The finite part is always in `A` (Proposition 4.1).

**The step that fails.** [A] needs `s(tau_(p_k)) = 0` exactly at some
`p_k > p_c`, and [Q] needs `l^q` summability. Neither condition is open in
`B`-norm: `A` is closed with empty interior in `B` for infinite `Gamma`, and
`l^q` is not `B`-closed. So `B`-norm continuity at `p_c`, weak* continuity,
and even exact membership at `p_c` do not propagate to any `p > p_c`.

**The precise witness.** Take the collapse family
`f_p = theta(p)^2 + (1 - theta(p)^2) tau_(p_c)` of
`fpbs-two-point-state-axioms-admit-collapse`. It satisfies (T1)–(T8), and also
the new facts `f_(p_c)` in `A` and `s(f_p) <= theta(p)^2 -> 0`. But `f_p` is
not in `c_0`, so it is not in `A`, and it is in no `l^q`, for every `p > p_c`.

Therefore the two-point state class, enlarged by Fourier-algebra membership
at `p_c` and by `B`-norm continuity, proves neither [A] nor [Q]. What is
missing is event-level: closability of the infinite-cluster form
`f -> E_p sum_(C infinite) |f(C)|^2` at some `p > p_c` (Corollary 2.3 with
Proposition 4.1). Under uniqueness it fails, because `tau_p >= theta^2` is not
in `c_0` (Theorem 3.1(2) with Theorem 2.1). Unboundedness of the form alone
is not the obstruction. For `p_(2->2) < p < p_2`, whenever that interval is
nonempty, the form is unbounded because `||T_p||_(2->2) = infinity`, yet it
is closable by Corollary 2.2. Closability is what separates
the witness from Bernoulli.

## 7. Not claimed

- [A] is not proved on any graph where `p_c < p_2` is unknown.
- It is not decided whether `{p : tau_p in A}` is an interval. Pointwise
  monotonicity of `tau_p` does not transfer to `A`-membership.
- No relation between `p_A` and `p_q` for `q > 2` is claimed beyond
  Calibration 5.5.
