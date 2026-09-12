# STW Problem I: one fixed pair in C*(PSL_2(Z)) is a universal test (2026-09-12)

Lane `quasitrace-modular`. Proof artifact for the claims
`stw01-modular-single-pair-quasitrace-additivity` and
`stw01-modular-test-pair-generates-non-exact-algebra`, and for the route
`stw01-problem-i-via-modular-single-pair`.

Notation as in `research/artifacts/stw01-modular-group-universal-test-2026-09-12.md`:
`Q = C^3 * C^2 = C*(Z_3 * Z_2) = C*(PSL_2(Z))`, the universal unital C*-algebra of a
partition of unity `e_1, e_2, e_3` and one projection `p`. Put

```text
h = e_1 p e_1,        k = e_1 p e_2 p e_1,        k_3 = e_1 p e_3 p e_1,
```

three positive elements of the corner `e_1 Q e_1`, tied by `h - h^2 = k + k_3`.
In group terms, with `u` of order 3, `s` of order 2 and `omega = exp(2 pi i / 3)`,
`e_j = (1 + omega^(-j) u + omega^(-2j) u^2) / 3` and `p = (1 + s) / 2`.

## 1. Review of the three-block dilation (Step 4' of the modular artifact): PASS

Checked line by line.

- `a = sum_i lambda_i e_i` with distinct `lambda_i in (0, 1)` is invertible, and
  `a - a^2 >= m 1` with `m = min_i lambda_i (1 - lambda_i)`.
- `b = m q <= m 1 <= a - a^2`, so `s_2 = b^(1/2)` and `s_3 = (a - a^2 - b)^(1/2)` exist,
  and `a, s_2, s_3` are self-adjoint.
- `c = (a, s_2, s_3)^T` gives `c* c = a^2 + b + (a - a^2 - b) = a`.
- `r = c a^(-1) c*` is self-adjoint and `r^2 = c a^(-1) (c* c) a^(-1) c* = r`.
- `r_ij = c_i a^(-1) c_j`, so `r_11 = a`, `r_12 = r_21 = s_2`. Hence
  `f_1 r f_1 = a (+) 0 (+) 0` and `f_1 r f_2 r f_1 = s_2^2 (+) 0 (+) 0 = b (+) 0 (+) 0`.
- If `g(0) = 0` then `g(a (+) 0 (+) 0) = g(a) (+) 0 (+) 0`.
- `e_1 p e_2 p e_1 = (e_2 p e_1)* (e_2 p e_1) >= 0`.
- The universal property of the unital full free product gives the unital surjection
  `pi : Q -> C*(1, f_1, f_2, f_3, r)`. Unital *-homomorphisms commute with continuous
  functional calculus.
- The 2-quasitrace property of `sigma = tau_3|_B o pi` uses the `6`-quasitrace on
  `M_6(M)` from (I3), through `M_2(pi)`.

Verdict: **PASS**. Remark used below: the dilation uses only that `a` is invertible
with `a - a^2 >= m 1` and that `q` is a projection, so it works in every unital
C*-algebra, not only in AW*-factors.

## 2. Theorem: a single-pair test

**Theorem.** The following are equivalent.

1. STW Problem I: every bounded 2-quasitrace on a unital C*-algebra is a trace.
2. Every bounded 2-quasitrace `sigma` on `C*(PSL_2(Z))` satisfies
   `sigma(h + k) = sigma(h) + sigma(k)` for the one fixed pair
   `h = e_1 p e_1`, `k = e_1 p e_2 p e_1`.

No functional calculus and no scalar parameter remain: the earlier witness shape
`sigma(g(h) + t k)` collapses to `g = id`, `t = 1`.

**Proof of (2) ⟹ (1).** Assume (1) fails.

*Step 0-3 (reviewed, unchanged).* They give a type `II_1` AW*-factor `M` with canonical
quasitrace `tau`, a projection `q in M`, `beta > 0`, and a finite-spectrum
`y = sum_(i=1)^k gamma_i e_i` with `gamma_1 > ... > gamma_k >= 0`, the `e_i` nonzero
pairwise orthogonal projections summing to `1`, such that

```text
D(y, beta q) = tau(y + beta q) - tau(y) - beta tau(q) != 0.
```

Here `gamma_1 > 0`: otherwise `y = 0` and `D(0, beta q) = 0` by homogeneity.

*Step A (affine rescaling with a tuned parameter).* For `eps in (0, 1/(2 gamma_1))` put

```text
lambda_i(eps) = 1/2 + eps gamma_i in [1/2, 1),     a_eps = sum_i lambda_i(eps) e_i = (1/2) 1 + eps y,
m(eps) = min_i lambda_i(eps) (1 - lambda_i(eps)) > 0.
```

The `lambda_i(eps)` are distinct, and `a_eps` is invertible. The function
`phi(eps) = m(eps) / eps` is continuous on `(0, 1/(2 gamma_1))`. As `eps -> 0+`,
`m(eps) -> 1/4`, so `phi -> +infinity`. As `eps -> (1/(2 gamma_1))-`,
`lambda_1(eps) -> 1`, so `m(eps) -> 0` and `phi -> 0`. By the intermediate value
theorem choose `eps` with `m(eps) = eps beta`. Fix it, and write `a = a_eps`,
`m = m(eps) = eps beta`.

*Step B (the defect after rescaling).* `tau` is homogeneous and additive on commuting
pairs, and `(1/2) 1` commutes with everything, so

```text
tau(a + m q)  = tau(1)/2 + eps tau(y + beta q),
tau(a)        = tau(1)/2 + eps tau(y),
tau(m q)      = eps beta tau(q).
```

Hence `tau(a + mq) - tau(a) - tau(mq) = eps D(y, beta q) != 0`.

*Step C (dilate and pull back).* Put `b = m q <= m 1 <= a - a^2`. Step 4' in `M_3(M)`
gives a projection `r` with `f_1 r f_1 = a (+) 0 (+) 0` and
`f_1 r f_2 r f_1 = m q (+) 0 (+) 0`. With `tau_3` from (I3), `B = C*(1, f_1, f_2, f_3, r)`
and the unital surjection `pi : Q -> B` (`e_j -> f_j`, `p -> r`), the bounded
2-quasitrace `sigma = tau_3|_B o pi` on `Q` satisfies

```text
pi(h) = a (+) 0 (+) 0,     pi(k) = m q (+) 0 (+) 0,
sigma(h + k) - sigma(h) - sigma(k) = tau(a + mq) - tau(a) - tau(mq) = eps D(y, beta q) != 0.
```

So (2) fails. **(1) ⟹ (2)** is trivial. ∎

**Remarks.**
- By the `e_2 <-> e_3` symmetry of `Q`, the pair `(h, e_1 p e_3 p e_1)` is an equally
  good test.
- The theorem is stated for `Q` itself. Transfer to groups surjecting onto
  `PSL_2(Z)` is not claimed at the level of a fixed pair, because the obvious lifts of
  `e_j` need not be projections in `C*(Gamma)`; linearity of all quasitraces still
  transfers, as recorded on `stw01-modular-group-algebra-quasitraces-are-traces`.

## 3. The test pair generates a non-exact algebra

**Claim.** `C*(h, k)`, the C*-subalgebra of `Q` generated by `h` and `k`, is not exact.

**Proof.** Apply Step 4' inside `A = Q` itself, which the Section 1 remark allows.
- Take `a = lambda_1 e_1 + lambda_2 e_2 + lambda_3 e_3` with distinct `lambda_i in (0, 1)`,
  `m = min_i lambda_i (1 - lambda_i)` and `b = m p`.
- This gives a projection `r in M_3(Q)` with `f_1 r f_1 = a (+) 0 (+) 0` and
  `f_1 r f_2 r f_1 = m p (+) 0 (+) 0`.
- The universal property gives a *-homomorphism `pi : Q -> M_3(Q)` with `e_j -> f_j` and
  `p -> r`, so `pi(h) = a (+) 0 (+) 0` and `pi(k) = m p (+) 0 (+) 0`.
- Hence `pi(C*(h, k)) = C*(a, p) (+) 0 (+) 0`.
- Since `sp(a) = {lambda_1, lambda_2, lambda_3}` avoids `0`, `C*(a)` contains `1` and the
  spectral projections `e_i`. So `C*(a, p) = C*(1, e_1, e_2, e_3, p) = Q`.

So `C*(h, k)` surjects onto a copy of `Q`. `Q` is not exact: `PSL_2(Z)` contains `F_2`,
the full algebra of a subgroup embeds in the full algebra of the group, and `C*(F_2)`
is not exact. Exactness passes to quotients (Kirchberg), so `C*(h, k)` is not exact. ∎

**Consequence.** Haagerup's theorem (2-quasitraces on exact C*-algebras are traces)
applies to no C*-subalgebra of any C*-algebra that contains both `h` and `k`. A proof
of the single-pair additivity must use more than exactness of an ambient subalgebra.
The corner algebra `e_1 Q e_1` contains a subalgebra mapping onto `Q` itself.

## 4. Additivity that holds for free (standard, recorded)

- `sigma` restricts to a trace on each `C*(e_j, p)` and on each `C*(e_i + e_j, p)`.
  These are quotients of `C^2 * C^2 = C*(D_infinity)`, which is nuclear.
- In particular `sigma(x + (h - h^2)) = sigma(x) + sigma(h - h^2)` for every
  `x in C*(h)_+`. So the pair `(h, k + k_3)` is additive, and the test is whether
  `k + k_3` can be split into `k` and `k_3`.
- Orthogonal positive pairs are additive.

## 5. Attempts, dead as stated

- **Exactness of an ambient subalgebra.** Dead by Section 3.
- **Two-projection subalgebras.** `sigma` is linear on every `C*(e_j, p)`, but `k` lies
  in none of them, and `C*(e_1, e_2, p) = Q`. The pair needs all three blocks.
- **Residual finite-dimensionality.** `Q` is RFD (Exel–Loring), but a non-linear
  quasitrace is not a weak* limit of finite-dimensional traces, since such limits are
  traces. RFD alone gives no additivity.
- **The `e_2 <-> e_3` symmetry.** `sigma o theta` is another 2-quasitrace, with test pair
  `(h, k_3)`. Without linearity, no relation between the two defects follows.
