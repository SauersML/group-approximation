---
rg: 2
id: thompson-f-iid-forest-test-vectors-are-bounded-below-one-proof
kind: route
title: Limit Rayleigh formula for product-form forest vectors, and the Hellinger idempotence gap H(nu, nu*nu) >= 1/8
target: thompson-f-iid-forest-test-vectors-are-bounded-below-one
requires: []
artifacts:
  - experiments/thompson-f-iid-forest-gap-2026-09-17/gap_audit.py
  - experiments/thompson-f-iid-forest-gap-2026-09-17/gap_audit.out
  - experiments/thompson-f-iid-forest-gap-2026-09-17/idempotence_scout.py
  - experiments/thompson-f-iid-forest-gap-2026-09-17/idempotence_scout.out
---

**Conventions.** These follow `thompson-f-norm-bound-from-forest-renewal-test-vector-proof`, steps 1 and 2, which
set up `G = <s_0, s_1> ≅ F`, the states `S_n`, the blocks, and the injective map `E : S_n -> G`.
- A product `g h` means "first `g`, then `h`". The move by generator `g` sends `E(x)` to `g E(x) = E(x) o g`.
- `(Kf)(z) = sum_g f(g z)` over `g in {s_0^{±1}, s_1^{±1}}`, and `P = K/4`.
- For a state in `S_n` and an integer `k`, `E(k)` is the left endpoint of the block of tree `i + k`. So
  `E(0) = a_i ∈ {0, ..., n-1}` and `E(1) = a_{i+1} ∈ {1, ..., n}`.

1. **Exact edge count.** Let `f` be supported on `E(S_n)`. Then `<f, K f> = Num_n`, the sum of `f(x) f(y)` over
   directed moves `x -> y` inside `S_n`.
   - The route cited above shows that each legal move is the Cayley edge `E(y) = g E(x)`, and that there is at most
     one per pair `(x, g)`. It remains to show that when the move is illegal, `g E(x)` lies outside `E(S_n)`.
   - `s_0` with `i = m-1`: `(E o s_0)(0) = E(1) = a_m = n`, which is not in `{0..n-1}`.
   - `s_0^{-1}` with `i = 0`: `(E o s_0^{-1})(0) = E(-1) = -1`, the left end of the outside leaf block `-1`.
   - `s_1` with `i = m-1`: `(E o s_1)(1) = E(2)`. This is the left end of block `m+1`, which is the outside leaf
     `[n+1, n+2]`, so `E(2) = n+1`, which is not in `{1..n}`.
   - `s_1^{-1}` with `T_i` a leaf: `(E o s_1^{-1})(1) = E(1/2) = a_i + 1/2`. This is not an integer, whereas every
     element of `E(S_n)` maps `1` to an integer.
   - Hence `<f, K f> = sum_{z} f(z) sum_g f(g z) = Num_n` exactly, and `<f, f> = D_n = sum_{S_n} f^2` by injectivity.

2. **Renewal identity for arbitrary weights.** Let `x, y` be real, finitely supported functions on trees with
   `x(leaf) != 0`, and let `f_n = y(T_i) prod_{j != i} x(T_j)`. Put
   - `p_s = sum_{|T|=s} x(T)^2`, `q_s = sum_{|T|=s} y(T)^2`, `B_s = sum_{|T|=s} x(T) y(T)`;
   - `M_j = sum_{|S|+|U|=j} y(S) x(U) y((S,U))`;
   - `Z_0 = 1`, `Z_k = sum_s p_s Z_{k-s}`.

   Split a state into the left trees, the pointer tree and the right trees. This gives
   `D_n = sum_{l+s+r=n} Z_l q_s Z_r`.

   Moves pair up as (pointer right, pointer left) and (merge, split), and each pair is a reversal. With `S = T_i`,
   `U = T_{i+1}` and `rest = prod_{j != i,i+1} x(T_j)^2`:
   - pointer right contributes `y(S)x(S) · x(U)y(U) · rest`;
   - merge contributes `[y(S) x(U)] · [y((S,U))] · rest`.

   Summing over shapes gives `Num_n = 2 sum_{l+j+r=n} Z_l H_j Z_r` with `H_j = sum_{s+t=j} B_s B_t + M_j`. This is
   the computation of the cited route, step 5, with `x` and `y` now arbitrary: that step never uses the special
   form of the weights, only that shape sums factor over independent trees.

3. **Tilt.** `p(t) = sum_s p_s t^s` is a polynomial with nonnegative coefficients, `p(0) = 0` and `p_1 = x(leaf)^2 > 0`.
   It is therefore strictly increasing on `[0, ∞)`, and there is a unique `r > 0` with `p(r) = 1`.
   - Replace `x(T), y(T)` by `r^{|T|/2} x(T)`, `r^{|T|/2} y(T)`.
   - Every state in `S_n` has `n` leaves in total, so `f_n` becomes `r^{n/2} f_n`, and the Rayleigh quotient is
     unchanged for every `n`.
   - From now on `sum_s p_s = 1`, and `mu = sum_s s p_s ∈ [1, ∞)`.

4. **Renewal asymptotics (elementary).**
   - As formal power series, `sum_k Z_k t^k = 1/(1 - p(t))`.
   - The root `t = 1` of the polynomial `1 - p` is simple, since `p'(1) = mu > 0`.
   - If `|ξ| <= 1` and `p(ξ) = 1`, then `1 = |sum p_s ξ^s| <= sum p_s |ξ|^s <= 1`. Equality forces `|ξ| = 1` and
     `ξ^s = 1` for every `s` in the support, and `s = 1` is in the support, so `ξ = 1`.
   - Partial fractions therefore give `1/(1-p(t)) = (1/mu)/(1-t) + R(t)`, where `R` is rational and has no poles in
     some disk `|t| < 1 + δ`. Hence `Z_k = 1/mu + e_k` with `|e_k| = O(θ^k)` for some `θ < 1`, and
     `sum |e_k| < ∞`.
   - `Y_k = sum_{l=0}^{k} Z_l Z_{k-l} = (k+1)/mu^2 + (2/mu) sum_{l<=k} e_l + sum_l e_l e_{k-l} = k/mu^2 + O(1)`.
   - `q` and `H` have finite support, so `D_n = sum_s q_s Y_{n-s} = n (sum q)/mu^2 + O(1)` and
     `Num_n = 2 sum_j H_j Y_{n-j} = 2 n (sum H)/mu^2 + O(1)`.
   - If `y != 0` then `sum q > 0`, and so `lim_n Num_n / D_n = 2 (sum_j H_j) / (sum_s q_s)`.

5. **Hilbert form.**
   - Put `u = x` (after the tilt, so `||u||^2 = sum p_s = 1`) and normalize `||y|| = 1`, that is, `sum q = 1`.
   - Then `sum_j sum_{s+t=j} B_s B_t = (sum_s B_s)^2 = <u, y>^2 = b^2`.
   - Also `sum_j M_j = sum_{S,U} y(S) u(U) y((S,U)) = <J(y ⊗ u), y> = m`. Here `J` maps `δ_S ⊗ δ_U` to
     `δ_{(S,U)}`, and since `(S,U) -> (S,U)` is a bijection of pairs onto non-leaf trees, `J` is an isometry.
   - With step 1, `lim_n <f_n, P f_n>/<f_n, f_n> = (1/4) · 2(b^2 + m) = (b^2 + m)/2`. This is part (a).
   - The objective `2(ΣX)^2/(ΣA ΣBq) + 2ΣM/(sqrt(ΣA) ΣBq)` of `split_ansatz.py` is this formula in unnormalized
     variables, and `gap_audit.py` reproduces the recorded optima `0.928967` (N=40) and `0.940020` (N=80) from it.

6. **Defects.** Let `u, y` be any unit vectors in `l^2(trees)`. Replacing `y` by `-y` changes neither `b^2` nor `m`
   (and only flips the sign of `f_n`), so assume `b >= 0`.
   - `eps_1 = ||y - u||` satisfies `b = 1 - eps_1^2/2`, and `eps_1^2 <= 2`.
   - `eps_2 = ||J(y⊗u) - y||` satisfies `m = 1 - eps_2^2/2`, because `||J(y⊗u)|| = ||y|| ||u|| = 1`.
   - By the triangle inequality, `||u - J(u⊗u)|| <= ||u - y|| + ||y - J(y⊗u)|| + ||J((y-u)⊗u)|| = 2 eps_1 + eps_2`.

7. **From trees to sizes.**
   - `J` permutes coordinates, so `|J(v)| = J(|v|)` and `|u ⊗ u| = |u| ⊗ |u|`. By the pointwise reverse triangle
     inequality, `||u - J(u⊗u)|| >= || |u| - J(|u|⊗|u|) ||`.
   - Let `π = u^2`, a probability law on trees, and `π' = J(|u|⊗|u|)^2`, the law of `(S,U)` for `S, U` i.i.d. `π`.
     Then `|| |u| - J(|u|⊗|u|) ||^2 = 2 - 2 sum_T sqrt(π_T π'_T)`.
   - Group the trees by size `k`. By Cauchy–Schwarz, `sum_{|T|=k} sqrt(π_T π'_T) <= sqrt(ν_k c_k)`, where
     `ν = |·|_* π` is the size law and `c = |·|_* π' = ν * ν`, since `|(S,U)| = |S| + |U|`.
   - Hence `2 eps_1 + eps_2 >= H := (sum_k (sqrt ν_k - sqrt c_k)^2)^{1/2}`.

8. **Hellinger to Fourier.**
   - `sum_k |ν_k - c_k| = sum_k |sqrt ν_k - sqrt c_k| (sqrt ν_k + sqrt c_k) <= H · ||sqrt ν + sqrt c|| <= 2H`.
   - With `φ(t) = sum_k ν_k e^{ikt}`, the characteristic function of `c` is `φ^2`, so for every `t`,
     `|φ(t) - φ(t)^2| <= sum_k |ν_k - c_k| <= 2H`.

9. **Fourier lemma.** For every probability law `ν` on the positive integers, `sup_t |φ(t) - φ(t)^2| >= 1/4`.
   - `φ` is continuous, because the series converges uniformly, and `φ(0) = 1`.
   - Its mean `(1/2π) ∫_0^{2π} φ(t) dt = ν_0 = 0`, so there is some `t_1` with `Re φ(t_1) <= 0`, and then
     `|1 - φ(t_1)| >= 1`.
   - `t -> |1 - φ(t)|` is continuous, equal to `0` at `t = 0` and at least `1` at `t_1`. By the intermediate value
     theorem there is `t*` with `|1 - φ(t*)| = 1/2`.
   - Then `|φ(t*)| >= 1/2`, so `|φ(t*) - φ(t*)^2| = |φ(t*)| |1 - φ(t*)| >= 1/4`.

10. **Constant.** Steps 6 to 9 give `2 eps_1 + eps_2 >= H >= 1/8`.
    - By Cauchy–Schwarz, `(2 eps_1 + eps_2)^2 <= 5 (eps_1^2 + eps_2^2)`, so `eps_1^2 + eps_2^2 >= 1/320`.
    - Since `eps_1^2 <= 2`,
      `2 - b^2 - m = eps_1^2 (1 - eps_1^2/4) + eps_2^2/2 >= (eps_1^2 + eps_2^2)/2 >= 1/640`.
    - Hence `(b^2 + m)/2 <= 1 - 1/1280`. This is part (b), and with step 5 it gives the theorem.

**Audit.** `gap_audit.py` evaluates `b, m, eps_1, eps_2, H_tree, H_size` and `sup_t |φ - φ^2|` (on a grid of 20001
points) for `params_N40.json` and `params_N80.json` of `experiments/thompson-f-norm-ansatz-2026-09-17`. It asserts
every inequality of the chain, and the output is in `gap_audit.out`. This is floating point, a consistency check on
the proof and not part of it.
