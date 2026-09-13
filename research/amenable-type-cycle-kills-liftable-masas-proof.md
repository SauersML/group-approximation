---
rg: 2
id: amenable-type-cycle-kills-liftable-masas-proof
kind: route
title: A Fourier character of the type cycle is central and almost invariant, and a small summed boundary forces its block averages to vanish
target: amenable-type-cycle-kills-liftable-masas
requires: []
---

Notation of the claim. Fix `n`, drop it from the notation, write `omega = exp(2 pi i j / L)` and
`f = f_j = sum_k omega^k e_k`. The trace `tau` is normalized, and `||x||_1 = tau(|x|)`.

**0. Traces.** `tau(e_(k+1)) = tau(V e_k V^*) = tau(e_k)`, so every `e_k` has trace `1/L`.

**1. Normalization.** `V A_n V^* = A_n` is a hypothesis at each stage, so `Ad V` maps
`A = prod_U A_n` onto itself.

**2. The characters are central and almost invariant.** `f` is a unitary in `Z(A_n)`, and
`V f V^* = sum_k omega^k e_(k+1) = omega^(-1) f`, using `omega^L = 1`. Hence `V^* f V = omega f` and
`||[V, f]||_2 = ||V f V^* - f||_2 = |1 - omega|`. If `j_n / L_n -> 0`, then `[f_(j_n)]` commutes
with `V` and lies in `A`, so it lies in `Q`. It commutes with all of `A >= Q`, so it lies in `Z(Q)`.

**3. Summed boundary.** Let `C = prod_U C_n <= Q` with `C_n` spanned by a partition `{q_A}`. Then
`eps_n^2 = sum_A ||[V_n, q_A]||_2^2 -> 0` along `U`.
- For signs `c_A in {+1, -1}` and `g = sum_A c_A q_A`, since `sum_B V q_B V^* = 1`,
  `||[V, g]||_2^2 = sum_(A,B) |c_A - c_B|^2 tau(q_A V q_B V^*)`.
- For independent uniform signs, `E|c_A - c_B|^2 = 2` for `A != B`, and
  `||[V, q]||_2^2 = 2 tau(q) - 2 tau(q V q V^*)`, so `E ||[V, g]||_2^2 = sum_A ||[V, q_A]||_2^2`.
- If `eps_n^2 >= delta > 0` on a `U`-large set, choose signs there with `||[V_n, g_n]||_2^2 >= delta`.
  Then `[g_n] in C` does not commute with `V`, contradicting `C <= Q`.

**4. One block.** Let `tau(q_A) > 0` and `x = q_A - V q_A V^*`, so `||x||_2 = ||[V, q_A]||_2`.
- `x = r x r` for the projection `r = q_A join V q_A V^*`, and `tau(r) <= 2 tau(q_A)`. So
  `||x||_1 = tau(r |x|) <= tau(r)^(1/2) ||x||_2 <= sqrt(2) tau(q_A)^(1/2) ||[V, q_A]||_2`.
- `tau(V q_A V^* f) = tau(q_A V^* f V) = omega tau(q_A f)`. So
  `|1 - omega| |tau(q_A f)| = |tau(x f)| <= ||x||_1`, because `f` is unitary.
- With `mu_A = tau(q_A f) / tau(q_A)`, which has `|mu_A| <= 1`:
  `tau(q_A) |mu_A| <= sqrt(2) tau(q_A)^(1/2) ||[V, q_A]||_2 / |1 - omega|`.

**5. Summing.** `E_(C_n) f = sum_A mu_A q_A`, and `f - E_(C_n) f` is orthogonal to `C_n`, so
`||f - E_(C_n) f||_2^2 = 1 - sum_A tau(q_A) |mu_A|^2`. Using `|mu_A|^2 <= |mu_A|`, step 4 and
Cauchy--Schwarz with `sum_A tau(q_A) = 1`:

```text
sum_A tau(q_A) |mu_A|^2  <=  sqrt(2) / |1 - omega| * sum_A tau(q_A)^(1/2) ||[V, q_A]||_2
                         <=  sqrt(2) eps_n / |1 - omega| .
```

This is item 3.

**6. Choice of frequency.** Put `j_n = max(1, ceil(L_n eps_n^(1/2)))`. Along `U`, `eps_n -> 0` and
`L_n -> infinity`, so `j_n / L_n -> 0` and `j_n <= L_n / 2` eventually. For `0 <= y <= 1/2`,
`|1 - exp(2 pi i y)| = 2 sin(pi y) >= 4 y`. Hence

```text
sqrt(2) eps_n / |1 - omega_(j_n)|  <=  sqrt(2) eps_n L_n / (4 j_n)  <=  sqrt(2) eps_n^(1/2) / 4  ->  0 .
```

So `f = [f_(j_n)]` has `||f_(j_n) - E_(C_n) f_(j_n)||_2 -> 1`, and `f` is not in `C`: if `f = [c_n]`
with `c_n in C_n`, then `||f_n - E_(C_n) f_n||_2 <= ||f_n - c_n||_2 -> 0`. By step 2, `f in Z(Q)`.

**7. No liftable masa.** A maximal abelian subalgebra of `Q` contains `Z(Q)`, since `Z(Q)` and the
algebra generate an abelian subalgebra of `Q`. Step 6 shows no liftable `C <= Q` contains `Z(Q)`.
This is item 2.

**8. Separable pieces (item 4).** Let `j_n / L_n -> 0` and `l_n = ceil((L_n / j_n)^(1/2))`. Partition
`Z/L_n` into consecutive intervals `I` of length `l_n` (one shorter interval allowed). Put
`q_I = sum_(k in I) e_k in Z(A_n)`.
- `tau(q_I V q_I V^*) = tau(q_I q_(I+1)) >= tau(q_I) - 1/L_n`, so
  `sum_I ||[V, q_I]||_2^2 <= 2 (L_n / l_n + 1) / L_n -> 0`. By step 3 read backwards (bounded
  coefficients: `||[V, sum_A c_A q_A]||_2^2 <= 2 sum_A ||[V, q_A]||_2^2` for `|c_A| <= 1`), `prod_U C_n`
  commutes with `V`. It lies in `prod_U Z(A_n) <= A`, so it lies in `Q`.
- On an interval the phase `omega^k` varies by at most `2 pi j_n l_n / L_n -> 0`, so
  `||f_(j_n) - E_(C_n) f_(j_n)||_2 -> 0` and `[f_(j_n)] in prod_U C_n`.

**9. The example.** `D_L (x) 1 (x) M_m` has center `D_L (x) 1 (x) 1`, which contains `e_k = e_(kk) (x) 1 (x) 1`,
and `S (x) 1 (x) 1` normalizes it and shifts the `e_k`. For `Gamma x|_alpha Z`, let `rho_0` be irreducible
with `rho_0 o alpha^(-L)` equivalent to `rho_0` and the `rho_k = rho_0 o alpha^(-k)`, `0 <= k < L`, pairwise
inequivalent. Put `sigma(gamma) = sum_k e_(kk) (x) rho_k(gamma) (x) 1_m` and let `sigma(t)` move level `k`
to level `k+1` by the identity, and level `L-1` to level `0` by an intertwiner `rho_L ~ rho_0`. This is a
representation. `sigma(Gamma)' = D_L (x) 1 (x) M_m` by Schur's lemma, and the ultraproduct commutant is
the ultraproduct of commutants by `at-op62-holds-for-representation-lifts` when `Gamma` is Kazhdan.
