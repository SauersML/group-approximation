# Klein-four symmetrization on the universal order-pair algebra (2026-09-16)

This artifact belongs to the hole `stw01-universal-order-pair-quasitrace-additivity`. It proves
two negative results about symmetry arguments on `U`, plus two elementary line lemmas:

- **Theorem 5.1.** The universal order-pair algebra `U` has a Klein four-group
  `K = {1, beta, gamma, beta gamma}` of automorphisms. The target is equivalent to additivity
  for `K`-invariant quasitraces alone, and even to one sign of the defect for them. So if
  Problem I fails, there are `K`-invariant witnesses with either sign.
- **Proposition 6.1.** For each `g` in `K` other than `1`, the identity "`sigma o g` reverses
  the defect for every `sigma`" is equivalent to Problem I. The mechanism that works in the
  three-projection algebra, where an automorphism reverses the defect unconditionally, is
  therefore not available through any element of `K` unless the problem is already solved.
  `U` has further automorphisms outside `K` (Section 7, "Not claimed"), and these are not
  analysed.
- **Lemmas 4.1 and 4.2.**
  - Lemma 4.1: a bounded 2-quasitrace is a trace iff it is affine along every line
    `t -> sigma(b + t a)`, iff its second differences along lines have one sign.
  - Lemma 4.2: a continuous function whose first differences of step `rho` are
    `kappa rho`-periodic for every `rho` is affine.

None of this decides the target. It is an obstruction to one family of attacks and a set of
normalizations for the others.

## 1. Setup

`U` is the universal unital C*-algebra of `h_0, k_0` with `0 <= h_0 <= 1` and
`0 <= k_0 <= c_0`, where `c_0 := h_0 - h_0^2`
(`research/artifacts/stw01-universal-order-pair-test-2026-09-12.md`).

`sigma` is a bounded 2-quasitrace on a unital C*-algebra `A`, and all arguments below are
self-adjoint. The proofs use only the following facts.

- **(F1) Commuting linearity.** `sigma` is real on `A_sa` and linear on the self-adjoint part of
  every abelian C*-subalgebra. Applied to `C*(1, w)` this gives:
  - (T) `sigma(w + alpha 1) = sigma(w) + alpha sigma(1)` for real `alpha`;
  - (O) `sigma(-w) = -sigma(w)`;
  - (H) `sigma(t w) = t sigma(w)` for `t >= 0`.
- **(F2) Monotonicity.** `a <= b` implies `sigma(a) <= sigma(b)`.
  - Haagerup states it as Corollary 3.4(1) in arXiv:1403.7653v1 (C. R. Math. Rep. Acad. Sci.
    Canada 36 (2014), 67–92), quoting Blackadar–Handelman 1982, Section II: a quasitrace is
    order preserving on `A_sa`. In that paper (Definition 3.1), "quasitrace" means a
    2-quasitrace.
  - It is also the axiom set of the repo audit
    `research/artifacts/stw01-quasitrace-status-and-local-permanence-audit-2026-08-30.md`
    ("Continuity trust boundary").
  - The original proof in Blackadar–Handelman 1982 was not fetched for this artifact.
- **(F3) Lipschitz bound.** `|sigma(a) - sigma(b)| <= ||a - b|| sigma(1)`, from (F2) and (T)
  (same audit).
- **(F4) Pullbacks and averages.**
  - If `pi : B -> A` is a unital *-homomorphism, then `sigma o pi` is a bounded 2-quasitrace on
    `B`, with 2-extension `sigma_2 o (pi (x) id_(M_2))`.
  - Nonnegative combinations of bounded 2-quasitraces are bounded 2-quasitraces, since every
    axiom, including the existence of the `M_2` extension, is preserved.
  - So for a finite group `G` of automorphisms of `B`, `(1/|G|) sum_g sigma o g` is a
    `G`-invariant bounded 2-quasitrace.

**Notation.**

```text
D_sigma(a, b) = sigma(a + b) - sigma(a) - sigma(b),
E_sigma(a, b) = sigma(b + a) + sigma(b - a) - 2 sigma(b),
phi_(a,b)(t)  = sigma(b + t a),
Delta_rho f(t)   = f(t + rho) - f(t),
Delta2_rho f(t)  = f(t + rho) + f(t - rho) - 2 f(t).
```

**Elementary identities.** Each follows from (T), (O), (H) and (F3).

- (1.1) `D` and `E` are unchanged when real scalars are added to either argument. Both are
  jointly positively homogeneous of degree 1, and `D(-a, -b) = -D(a, b)`, `E(-a, -b) = -E(a, b)`.
- (1.2) `E(a, b) = D(a, b) + D(a - b, b)`. Indeed the right side is
  `sigma(a + b) - sigma(a - b) - 2 sigma(b)`, and `sigma(a - b) = -sigma(b - a)`.
- (1.3) `E(a, b) = Delta2_1 phi_(a,b)(0)`.
- (1.4) `|E(a, b) - E(a, b')| <= 4 ||b - b'|| sigma(1)` and
  `|D(a, b) - D(a, b')| <= 2 ||b - b'|| sigma(1)`.
- (1.5) `phi_(a,b)` is continuous, and `|Delta_p phi_(a,b)(t)| <= |p| ||a|| sigma(1)`.

**Lemma 1.1 (rescaled order pairs).** Let `x, y` be self-adjoint contractions in a unital `A`.

- (i) Put `lambda = 1/4`, `s = 3/32`, `0 < eps <= 1/20`.
- (ii) Put `lambda = 1/2`, `s = 1/8`, `0 < eps <= 1/10`.

In either case `h := lambda + eps x` and `k := s + eps y` satisfy `0 <= h <= 1` and
`0 <= k <= h - h^2`. So there is a unital *-homomorphism `pi : U -> A` with `pi(h_0) = h` and
`pi(k_0) = k`.

*Proof.* In both cases `sp(h)` lies in `[lambda - eps, lambda + eps]`, inside `[0, 1]`, and
`k >= s - eps >= 0`. We have `h - h^2 = lambda(1 - lambda) + eps mu x - eps^2 x^2` with
`mu := 1 - 2 lambda`.

- (i) `h - h^2 >= 3/16 - eps/2 - eps^2` and `k <= 3/32 + eps`. Then
  `3/32 + eps <= 3/16 - eps/2 - eps^2` because `(3/2) eps + eps^2 <= 0.0775 <= 3/32`.
- (ii) `h - h^2 >= 1/4 - eps^2` and `k <= 1/8 + eps`, and `1/8 + eps + eps^2 <= 0.235 <= 1/4`.

The homomorphism comes from universality. This is the rescaling of
`stw01-order-pair-defects-rescale-generic-defects`, with the centre `lambda = 1/4` also allowed.
`square`

## 2. The Klein four-group of `U`

**Lemma 2.1.** Two assignments extend to unital *-endomorphisms of `U`:

```text
beta :  h_0 -> 1 - h_0,   k_0 -> k_0,
gamma:  h_0 -> h_0,       k_0 -> c_0 - k_0.
```

They are commuting involutions, hence automorphisms. `K = {1, beta, gamma, beta gamma}` is a
Klein four-group, and `beta gamma` sends `h_0 -> 1 - h_0`, `k_0 -> c_0 - k_0`.

*Proof.*

- **Relations are preserved.** `(1 - h_0) - (1 - h_0)^2 = h_0 - h_0^2 = c_0`, so `beta` preserves
  the relations. Also `0 <= c_0 - k_0 <= c_0`. By universality both maps exist.
- **Each fixes `c_0`.** `beta(c_0) = c_0`, and `gamma` fixes `h_0`, hence `c_0`.
- **Involutions.** `beta^2` and `gamma^2` fix the generators, since
  `gamma^2(k_0) = c_0 - (c_0 - k_0) = k_0`.
- **They commute.** `beta gamma (k_0) = beta(c_0 - k_0) = c_0 - k_0 = gamma beta (k_0)`, and both
  send `h_0` to `1 - h_0`.
- **The three maps are distinct and nontrivial.** Compose with characters of `U`:
  - `h_0 -> 1/2, k_0 -> 0` sends `k_0` and `gamma(k_0)` to `0` and `1/4`, so `gamma` and
    `beta gamma` differ from `1` and from `beta`.
  - `h_0 -> 0, k_0 -> 0` separates `h_0` from `beta(h_0)`.

`square`

**Where `gamma` lives in `Q = C*(PSL_2(Z))`.** In the model `U ~= C*(1, h, k)` of Theorem A,
with `h = e_1 p e_1`, `k = e_1 p e_2 p e_1` and `h - h^2 = k + k_3`, the automorphism `gamma`
is the restriction of the swap `e_2 <-> e_3`, which fixes `e_1` and `p` and sends `k` to `k_3`.

The map `p -> 1 - p` sends `h` to `e_1 - h` and fixes `k`. It realizes `beta` only inside the
corner with unit `e_1`, and is not used below.

**Lemma 2.2 (defect transformation).** For every bounded 2-quasitrace `rho` on `U`:

```text
D_(rho o beta)      (h_0, k_0) = D_rho(h_0 - k_0,     k_0),
D_(rho o gamma)     (h_0, k_0) = D_rho(h_0,           c_0 - k_0),
D_(rho o beta gamma)(h_0, k_0) = D_rho(h_0^2 + k_0,   c_0 - k_0),
D_rho(h_0, k_0) + D_(rho o beta)(h_0, k_0) = E_rho(h_0, k_0).
```

*Proof.*

- **`beta`.** By (T) and (O),
  `D_rho(1 - h_0, k_0) = [rho(1) - rho(h_0 - k_0)] - [rho(1) - rho(h_0)] - rho(k_0)`, which is
  `D_rho(h_0 - k_0, k_0)`.
- **`gamma`.** Immediate.
- **`beta gamma`.**
  `D_rho(1 - h_0, c_0 - k_0) = rho(1 - (h_0^2 + k_0)) - rho(1 - h_0) - rho(c_0 - k_0)`, which is
  `rho(h_0) - rho(h_0^2 + k_0) - rho(c_0 - k_0)`, and that is `D_rho(h_0^2 + k_0, c_0 - k_0)`.
- **Last line.** This is (1.2).

`square`

## 3. Pulled-back Klein defects

**Lemma 3.1.** Let `tau` be a bounded 2-quasitrace on a unital `A`, and `x, y` self-adjoint
contractions. Take `lambda, s, eps, pi` as in Lemma 1.1, and put `mu = 1 - 2 lambda` and

```text
w_eps := mu x - y - eps x^2.
```

Then

```text
D_(tau o pi)          (h_0, k_0) = eps D_tau(x, y),
D_(tau o pi o beta)   (h_0, k_0) = eps D_tau(x - y, y),
D_(tau o pi o gamma)  (h_0, k_0) = eps D_tau(x, w_eps),
D_(tau o pi o beta gamma)(h_0, k_0) = eps D_tau(x - w_eps, w_eps),
sum_(g in K) D_(tau o pi o g)(h_0, k_0) = eps [ E_tau(x, y) + E_tau(x, w_eps) ].
```

*Proof.* Apply Lemma 2.2 to `rho = tau o pi`, and use `D_(tau o pi)(u, v) = D_tau(pi(u), pi(v))`.
The images are:

```text
pi(h_0)              = lambda + eps x,
pi(k_0)              = s + eps y,
pi(h_0 - k_0)        = (lambda - s) + eps (x - y),
pi(c_0 - k_0)        = (lambda(1 - lambda) - s) + eps w_eps,
pi(h_0^2 + k_0)      = pi(h_0 - (c_0 - k_0)) = (lambda - lambda(1 - lambda) + s) + eps (x - w_eps).
```

By (1.1), `D_tau(alpha + eps u, beta + eps v) = eps D_tau(u, v)`. For the sum, group the terms
in pairs, `D(x, y) + D(x - y, y)` and `D(x, w) + D(x - w, w)`, and apply (1.2) to each. `square`

The script `experiments/stw01-order-pair-klein-symmetrization-2026-09-16/check_klein_defects.py`
checks these identities numerically, in floating point, with maximum error `9.8e-15`. It uses
random `6 x 6` Hermitian contractions and nonlinear test functionals. Those functionals satisfy
(T), (O), (H), the only properties the algebra uses, but they are not quasitraces. Its output is
`output.txt` next to it.

**Remark 3.2 (the centre `lambda = 1/2` is degenerate).** Take `lambda = 1/2`, so `mu = 0`.

- **Exact `beta` formula.** Here `D_(tau o pi) + D_(tau o pi o beta) = eps E_tau(x, y)`, with no
  remainder.
- **`beta gamma` cancels to first order.** `D(x, y) + D(x + y, -y) = 0` identically, by (O). With
  `w = y + eps x^2` and (1.4),

  ```text
  |D_(tau o pi) + D_(tau o pi o beta gamma)| = eps |D(x, y) + D(x + w, -w)| <= 2 eps^2 ||x||^2 tau(1).
  ```

- **The Klein sum is second order.** Since `E(x, -v) = -E(x, v)`, the Klein sum is
  `eps [E(x, y) - E(x, y + eps x^2)]`, of size at most `4 eps^2 ||x||^2 tau(1)`.

So at the centre `1/2`, symmetrizing suppresses the first-order information. That is why
Theorem 5.1 uses `lambda = 1/4`. The script shows the `O(eps^2)` behaviour numerically: the
ratio `|D_1 + D_(beta gamma)| / eps^2` is `0.360`, `0.321` and `0.317` at
`eps = 1e-1, 1e-2, 1e-3`, for one random pair and one test functional.

## 4. Two line lemmas

**Lemma 4.1 (line criterion).** For a bounded 2-quasitrace `sigma` on a unital `A`, the
following are equivalent:

- (a) `sigma` is a trace;
- (b) every `phi_(a,b)` (`a, b in A_sa`) is affine;
- (c) `E_sigma(a, b) = 0` for all `a, b in A_sa`;
- (d) `E_sigma(a, b) >= 0` for all `a, b in A_sa`;
- (d') `E_sigma(a, b) <= 0` for all `a, b in A_sa`.

*Proof.*

- **(a) implies (c), and (c) implies (d) and (d').** Trivial.
- **(d') implies (d).** `E(-a, -b) = -E(a, b)`.
- **(d) implies (b).**
  - Fix `a, b` and put `phi = phi_(a,b)`. For real `t` and `r > 0`, the pair `(r a, b + t a)`
    gives `E(r a, b + t a) = Delta2_r phi(t) >= 0`. So `phi` is midpoint convex, and by (1.5)
    continuous, hence convex.
  - The same applies to `phi_(a,-b)(t) = sigma(-b + t a) = -phi(-t)`, by (O). So
    `t -> -phi(-t)` is convex, which means `phi` is concave.
  - Convex and concave functions are affine.
- **(b) implies (a).**
  - Write `phi_(a,b)(t) = sigma(b) + m t`. For `t > 0`, (H) and (F3) give
    `|phi(t) - t sigma(a)| = |sigma(b + t a) - sigma(t a)| <= ||b|| sigma(1)`, so `m = sigma(a)`.
  - At `t = 1` this is `sigma(a + b) = sigma(a) + sigma(b)`.
  - With `sigma(a + i b) = sigma(a) + i sigma(b)`, `sigma` is linear, and
    `sigma(x^* x) = sigma(x x^*) >= 0` makes it a trace.

`square`

This is a per-quasitrace companion of Proposition 4.1 of
`research/artifacts/stw01-certificates-products-universal-tests-2026-09-11.md`, which covers
subadditivity and superadditivity. Novelty beyond this repository is not claimed.

**Lemma 4.2 (periodic differences).** Let `f : R -> R` be continuous, with
`sup_t |Delta_p f(t)| < infinity` for every `p`.

- (i) Suppose there is `kappa != 0` such that, for every `rho > 0`, `Delta_rho f` has period
  `kappa rho`. Then `f` is affine.
- (ii) Suppose there is `nu != 0` such that

  ```text
  Delta2_rho f(t) = Delta2_rho f(t - nu rho)        for all t in R, rho > 0.          (4.2.1)
  ```

  Then the hypothesis of (i) holds with `kappa = nu`, so `f` is affine.

*Proof of (ii).*

- Fix `rho > 0`, put `p = nu rho` and `chi = Delta_p f`. This function is continuous and
  bounded.
- `Delta2_rho` commutes with translations. Applying (4.2.1) at `t + p` gives
  `Delta2_rho chi(t) = Delta2_rho f(t + p) - Delta2_rho f(t) = 0`.
- So for each `t` the sequence `n -> chi(t + n rho)` on `Z` has vanishing second differences.
  It is therefore `chi(t) + n (chi(t + rho) - chi(t))`, and boundedness forces
  `chi(t + rho) = chi(t)`.
- Written out, `f(t + rho + p) - f(t + rho) = f(t + p) - f(t)` for all `t`. Equivalently
  `f(t + p + rho) - f(t + p) = f(t + rho) - f(t)`, so `Delta_rho f` has period `p = nu rho`.

*Proof of (i).*

- Fix `rho > 0` and `n >= 1`. Then
  `Delta_rho f(t) = sum_(j=0)^(n-1) Delta_(rho/n) f(t + j rho / n)`.
- By hypothesis each summand has period `kappa rho / n` in `t`, so `Delta_rho f` does too.
- The periods of a continuous function form a closed subgroup of `R`. This one contains the
  nonzero numbers `kappa rho / n`, which tend to `0`, so it is `R`.
- Hence `Delta_rho f` is a constant `c(rho)`.
- Telescoping gives `c(rho + rho') = c(rho) + c(rho')`, and `c(rho) = f(rho) - f(0)` is
  continuous. So `c(rho) = m rho`.
- Thus `f(t) = f(0) + m t` for `t > 0`. For `t < 0`, `f(0) - f(t) = c(-t) = -m t`.

`square`

By (1.5), every line function `phi_(a,b)` of a bounded 2-quasitrace satisfies the regularity
hypotheses of Lemma 4.2.

## 5. Klein-invariant witnesses

**Theorem 5.1.** The following are equivalent:

- (i) every bounded 2-quasitrace on every unital C*-algebra is a trace;
- (ii) every bounded 2-quasitrace `sigma` on `U` satisfies `D_sigma(h_0, k_0) = 0` (the target);
- (iii) every `K`-invariant bounded 2-quasitrace `sigma` on `U` satisfies
  `D_sigma(h_0, k_0) = 0`;
- (iv) every `K`-invariant bounded 2-quasitrace `sigma` on `U` satisfies
  `D_sigma(h_0, k_0) <= 0`;
- (iv') every `K`-invariant bounded 2-quasitrace `sigma` on `U` satisfies
  `D_sigma(h_0, k_0) >= 0`.

In particular, if (i) fails then some `K`-invariant bounded 2-quasitrace on `U` has
`D(h_0, k_0) > 0`, and another has `D(h_0, k_0) < 0`.

*Proof.* The implications (i) => (ii) => (iii) => (iv) and (iii) => (iv') are trivial. We prove
(iv) => (i); the case (iv') is the same with every inequality reversed.

- **Step 1: symmetrize.**
  - Let `tau` be a bounded 2-quasitrace on a unital `A`, and `x, y` self-adjoint contractions.
  - For `0 < eps <= 1/20` take `pi` as in Lemma 1.1(i) (`lambda = 1/4`, `mu = 1/2`), and put
    `sigma_eps := (1/4) sum_(g in K) tau o pi o g`.
  - By (F4), `sigma_eps` is a `K`-invariant bounded 2-quasitrace on `U`.
  - The defect is linear in the functional, so by Lemma 3.1
    `4 D_(sigma_eps)(h_0, k_0) = eps [E_tau(x, y) + E_tau(x, w_eps)]`, with
    `w_eps = x/2 - y - eps x^2`.
  - By (iv), `E_tau(x, y) + E_tau(x, w_eps) <= 0`.
- **Step 2: let `eps -> 0`.**
  - By (1.4), `|E_tau(x, w_eps) - E_tau(x, x/2 - y)| <= 4 eps ||x||^2 tau(1)`. Hence

    ```text
    E_tau(x, y) + E_tau(x, x/2 - y) <= 0         for all self-adjoint contractions x, y.   (5.1.1)
    ```

  - Applying (5.1.1) to `(-x, -y)` changes the sign of both terms, by (1.1). So equality holds.
  - By joint homogeneity it holds for all `x, y in A_sa`.
- **Step 3: rewrite along a line.**
  - Let `phi = phi_(x,y)`. By (1.3), `E_tau(x, y) = Delta2_1 phi(0)`.
  - By (O),

    ```text
    E_tau(x, x/2 - y) = tau(3x/2 - y) + tau(-x/2 - y) - 2 tau(x/2 - y)
                      = -[phi(-3/2) + phi(1/2) - 2 phi(-1/2)] = -Delta2_1 phi(-1/2).
    ```

  - Hence `Delta2_1 phi_(x,y)(0) = Delta2_1 phi_(x,y)(-1/2)` for all `x, y in A_sa`.
- **Step 4: rescale the line.**
  - For `t_0 in R` and `rho > 0`, apply the last identity to the pair `(rho x, y + t_0 x)`. Its
    line function is `u -> phi(t_0 + rho u)`.
  - This gives `Delta2_rho phi(t_0) = Delta2_rho phi(t_0 - rho/2)`, which is (4.2.1) with
    `nu = 1/2`.
- **Step 5: conclude.** By Lemma 4.2, every `phi_(x,y)` is affine. By Lemma 4.1, `tau` is a
  trace. `square`

**Corollary 5.2.**

- For any `H` among `{1, beta}`, `{1, gamma}`, `{1, beta gamma}` and `K`, the target is
  equivalent to additivity, or to either one-sided inequality, for `H`-invariant bounded
  2-quasitraces on `U`. This follows from Theorem 5.1, because `K`-invariance implies
  `H`-invariance.
- A proof of the target may therefore assume `sigma o beta = sigma o gamma = sigma`. A
  counterexample search may assume the same, and may prescribe the sign of the defect.

## 6. No element of `K` reverses the defect unconditionally

**Proposition 6.1.** Let `g in {beta, gamma, beta gamma}`. Consider

```text
D_(sigma o g)(h_0, k_0) + D_sigma(h_0, k_0) <= 0     for every bounded 2-quasitrace sigma on U.   (R_g)
```

Condition (R_g), its reverse, and the equality version "`sigma o g` reverses the defect" are each
equivalent to (i) of Theorem 5.1.

*Proof.* (i) makes every defect zero, so it implies all three versions. Conversely, assume
(R_g). The reversed inequality is handled the same way. Fix `tau` on `A` and self-adjoint
contractions `x, y`, and pull back along `pi` from Lemma 1.1.

- **`g = beta`.**
  - By Lemma 3.1 and (1.2), `D_(tau o pi) + D_(tau o pi o beta) = eps E_tau(x, y)`, at either
    centre. So `E_tau(x, y) <= 0`.
  - Replace `(x, y)` by `(-x, -y)` to get equality, and extend by homogeneity.
  - Lemma 4.1(c) gives (i).
- **`g = gamma`, centre `1/2`.**
  - Here `w_eps = -y - eps x^2`, and `D_(tau o pi) + D_(tau o pi o gamma)` equals
    `eps [D(x, y) + D(x, -y - eps x^2)]`.
  - By (1.4), letting `eps -> 0` gives `D(x, y) + D(x, -y) <= 0`.
  - The left side is `tau(x + y) + tau(x - y) - 2 tau(x) = E_tau(y, x)`.
  - Sign reversal and homogeneity give `E_tau = 0`, and Lemma 4.1 gives (i).
- **`g = beta gamma`, centre `1/4`.** Remark 3.2 shows the centre `1/2` carries no first-order
  information for this `g`.
  - With `w_eps = x/2 - y - eps x^2`, the sum `D_(tau o pi) + D_(tau o pi o beta gamma)` equals
    `eps [D(x, y) + D(x - w_eps, w_eps)]`.
  - The map `w -> D(x - w, w) = tau(x) - tau(x - w) - tau(w)` is `2 tau(1)`-Lipschitz, so the
    limit is `D(x, y) + D(x/2 + y, x/2 - y) <= 0`.
  - By (O) the left side is `phi(1) - phi(0) - phi(1/2) + phi(-1/2)`, with `phi = phi_(x,y)`.
    That is `Delta_(1/2) phi(1/2) - Delta_(1/2) phi(-1/2)`.
  - Sign reversal and homogeneity give equality for all `x, y in A_sa`.
  - Apply it to `(rho x, y + t_0 x)`. Then `Delta_(rho/2) phi(t_0 + rho/2) = Delta_(rho/2) phi(t_0 - rho/2)`,
    so `Delta_q phi` has period `2q` for every `q > 0`.
  - Lemma 4.2(i) with `kappa = 2`, followed by Lemma 4.1, gives (i).

`square`

**Remark 6.2 (contrast with the three-projection algebra).**

- **`P_3`.** In the sibling lane
  (`notes/stw01-three-projection-algebra-quasitrac-swarm-2026-09-16.md`, its Lemma 4.1), the
  automorphism `r_2 -> 1 - r_2`, `r_3 -> 1 - r_3` reverses the corner-pair defect for every
  quasitrace. There a counterexample is never invariant under it. That lemma is not re-verified
  here.
- **Why the flip works there.** The symmetry replaces each corner element by its complement
  inside a commutative corner, and the complement flip `D(1 - a, 1 - b) = -D(a, b)` does the rest.
- **Why it fails on `U`.** Each nontrivial `g in K` replaces `(h_0, k_0)` by a genuinely
  different pair: `(h_0 - k_0, k_0)`, `(h_0, c_0 - k_0)` or `(h_0^2 + k_0, c_0 - k_0)`. These are
  related to the original pair only through first or second differences along lines. By
  Proposition 6.1, turning any of these relations into a reversal is already Problem I.

## 7. What this kills, and what is not claimed

**Dead routes.**

- **Symmetrization over `K`.** Any argument that averages a quasitrace over `beta`, `gamma` or
  `beta gamma` and expects the defect to cancel. The first-order cancellation at the centre
  `1/2` (Remark 3.2) is an artefact of that centre. At the centre `1/4` it disappears
  (Theorem 5.1).
- **The `P_3` mechanism.** Any argument that looks for a contradiction from invariance under a
  subgroup of `K`, or that tries to prove a reversal identity for one of these automorphisms,
  as in `P_3`. By Proposition 6.1 the reversal is the whole problem.

**Normalizations gained.**

- **Witnesses.** Witnesses may be taken `K`-invariant with a prescribed sign.
- **Problem I along lines.** Problem I is equivalent to each of the following, for all bounded
  2-quasitraces and all lines `phi_(x,y)`:
  - `Delta2_rho phi` is `rho/2`-periodic for every `rho`;
  - `Delta_q phi` is `2q`-periodic for every `q`;
  - `phi` is midpoint convex.

  These are reformulations, not progress.

**Not claimed.**

- Nothing about the truth of the target.
- Nothing about the fixed-point algebra `U^K`. A `K`-invariant quasitrace is not known to be
  determined by its restriction to `U^K`, because the averaging map `(1/4) sum g` is not
  multiplicative and `sigma` is not linear.
- **Nothing about automorphisms outside `K`.** `K` is not the whole automorphism group of `U`.
  - **Inner automorphisms.** They exist, but they are invisible: `sigma o Ad u = sigma`, from
    `sigma(x^* x) = sigma(x x^*)` and (T).
  - **The maps `psi_f`.** Let `f : [0, 1] -> [0, 1]` be a homeomorphism such that
    `q_f(lambda) := (f(lambda) - f(lambda)^2) / (lambda - lambda^2)` on `(0, 1)` extends to a
    continuous, strictly positive function on `[0, 1]`. Examples are the `C^1` diffeomorphisms
    with nonzero derivative at both endpoints.
    - Put `g_f := q_f^(1/2)`. The elements `f(h_0)` and `g_f(h_0) k_0 g_f(h_0)` satisfy the
      defining relations, because
      `0 <= g_f(h_0) k_0 g_f(h_0) <= g_f(h_0) c_0 g_f(h_0) = f(h_0) - f(h_0)^2`. So universality
      gives an endomorphism `psi_f`.
    - `q_(f^(-1))(lambda) = 1 / q_f(f^(-1)(lambda))`, so `g_(f^(-1))(f(lambda)) g_f(lambda) = 1`.
      Hence `psi_f o psi_(f^(-1)) = id`, and by symmetry the other composite is the identity too.
      So `psi_f` is an automorphism.
    - `beta = psi_f` for `f(lambda) = 1 - lambda`, and `gamma` is not of this form.
  - **What is open.** `D_(sigma o psi_f)(h_0, k_0) = D_sigma(f(h_0), g_f(h_0) k_0 g_f(h_0))` is
    not related to `D_sigma(h_0, k_0)` by (T), (O) and (H) when `f` is not affine. Proposition
    6.1 says nothing about these automorphisms, or about the group they generate with `gamma`.

## 8. Verification and trust boundary

- **Numerical check.** The algebraic identities of Lemmas 2.2 and 3.1, Remark 3.2, and the
  limiting line identities of Theorem 5.1 and Proposition 6.1 are checked by the script above.
  - 200 random pairs, two functionals, maximum error `9.8e-15`.
  - Minimum spectral margin `2.3e-2` for the order relations of Lemma 1.1(i) at `eps = 1/20`.
  - The script tests only algebra that holds for any functional with (T), (O), (H). It cannot
    test the analytic Lemmas 4.1 and 4.2 or the `eps -> 0` limits, which are proved above.
- **Trust boundary.**
  - Only (F1)–(F4) are used.
  - (F2) is the one quoted property.
  - Neither Haagerup's exactness theorem nor the Gow AW*-factor reduction is used anywhere in
    Sections 1–6.

## 9. Sources

- STW Problem I status, as recorded in
  `research/artifacts/stw01-quasitrace-status-and-local-permanence-audit-2026-08-30.md`.
- A same-day (2026-09-16) arXiv API query for `all:quasitrace` returned the newest relevant
  item arXiv:2601.04431v2 (A. Gow, "On the Quasitrace Problem and a Characterization of
  W*-algebras", v1 2026-01-07, v2 2026-07-14), which frames the question as open.
- The withdrawn arXiv:2501.13088v2 (Gow).
- arXiv:2309.17412v2 (Milhøj–Rørdam, "Around traces and quasitraces", 2023-11-30).
- arXiv:1403.7653v1 (Haagerup, "Quasitraces on exact C*-algebras are traces", C. R. Math. Rep.
  Acad. Sci. Canada 36 (2014), 67–92), from text extracted on 2026-09-16. Used: the introduction
  (the Blackadar–Handelman `2 => n` quotation), Definition 3.1, and Corollary 3.4 (order
  preservation on `A_sa`, and extension to `M_n(A)`, quoted from Blackadar–Handelman Section II).
  That is the source for (F2).
- arXiv:2609.10218v1 (Arulseelan–Hanson), reported by the sibling lane's gate, not
  independently fetched here.
- Blackadar–Handelman 1982 was not fetched. It is used only through Haagerup's quotation
  (Corollary 3.4) for (F2).
