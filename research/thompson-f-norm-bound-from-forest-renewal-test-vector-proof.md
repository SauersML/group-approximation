---
rg: 2
id: thompson-f-norm-bound-from-forest-renewal-test-vector-proof
kind: route
title: A product-form nonnegative test vector on pointed-forest windows, evaluated exactly by a renewal recursion
target: thompson-f-norm-bound-from-forest-renewal-test-vector
requires: []
artifacts:
  - experiments/thompson-f-norm-ansatz-2026-09-17/certify_window.py
  - experiments/thompson-f-norm-ansatz-2026-09-17/certify_selftest.out
  - experiments/thompson-f-norm-ansatz-2026-09-17/split_ansatz_N40_N80.out
  - experiments/thompson-f-norm-ansatz-2026-09-17/params_N80.json
  - experiments/thompson-f-norm-ansatz-2026-09-17/certificate_N80_n30000.json
  - experiments/thompson-f-norm-ansatz-2026-09-17/certify_N80_n30000_json.out
  - experiments/thompson-f-norm-ansatz-2026-09-17/params_N40.json
  - experiments/thompson-f-norm-ansatz-2026-09-17/certificate_N40_n20000.json
  - experiments/thompson-f-norm-ansatz-2026-09-17/certify_N40_n20000_json.out
  - experiments/thompson-f-norm-ansatz-2026-09-17/model_check.py
  - experiments/thompson-f-norm-ansatz-2026-09-17/model_check.out
---

Notation: a product `g h` in a group of maps means "first `g`, then `h`", that is `h o g`.
`K = s_0 + s_0^{-1} + s_1 + s_1^{-1}`, acting on `l^2(G)` by `(Kf)(x) = sum_g f(g x)` over the
four generators. This is `sum_g lambda(g)` (the generating set is symmetric), so
`||K|| = 4||P||`.

1. **The group.** In `PL(R)` put `s_0(t) = t + 1`, and `s_1(t) = t` for `t <= 0`, `2t` on
   `[0,1]`, `t + 1` for `t >= 1`. Let `G = <s_0, s_1>`.
   - `model_check.py` (`check_relations`, exact rational PL arithmetic) verifies
     `[s_0 s_1^{-1}, s_0^{-1} s_1 s_0] = [s_0 s_1^{-1}, s_0^{-2} s_1 s_0^2] = 1` and `s_0 s_1 != s_1 s_0`.
   - These are the relators of Cannon–Floyd–Parry's presentation
     `F = <A, B | [AB^{-1}, A^{-1}BA], [AB^{-1}, A^{-2}BA^2]>` (Enseign. Math. 42 (1996), Thm 3.4),
     so `A -> s_0`, `B -> s_1` defines a surjection `F -> G`.
   - Its image is nonabelian, and every proper quotient of `F` is abelian (CFP Thm 4.3), so it is an
     isomorphism.

   Composition conventions do not matter here. If the relators held only in the opposite group,
   then `G^op ≅ F`, and inversion `G -> G^op` preserves the symmetric generating set and the norm.
   Hence `||K||` is the norm of `x_0 + x_0^{-1} + x_1 + x_1^{-1}` in `C*_r(F)`.

2. **Forest window embedding.**
   - *States.* `S_n` is the set of pairs `(T_0, ..., T_{m-1}; i)`: finite binary trees with
     `sum |T_j| = n` leaves in total, and `0 <= i < m`.
   - *Tree maps.* For a tree `T` let `h_T: [0,1] -> [0,|T|]` be the PL map with `h_leaf(t) = t`, and
     `h_{(L,R)}(t) = h_L(2t)` on `[0,1/2]`, `|L| + h_R(2t-1)` on `[1/2,1]`.
   - *Blocks.* Extend the forest by single leaves: tree `j < 0` is a leaf with block `[j, j+1]`, and
     tree `j >= m` is a leaf with block `[n+j-m, n+j-m+1]`. Tree `j` in `0..m-1` has block
     `[a_j, a_j + |T_j|]` with `a_j = sum_{k<j} |T_k|`.
   - *The element.* `E(state)` is the PL homeomorphism of `R` that maps `[k, k+1]` onto the block of
     tree `j = i + k` by `t -> a_j + h_{T_j}(t - k)`, for every `k in Z`.

   The four moves and their effect on `E`:
   - *Pointer right* (`i + 1 < m`). `E(x) o s_0` maps `[k,k+1]` onto block `i+k+1`, so it is
     `E` of the same forest with pointer `i+1`.
   - *Merge* (`i + 1 < m`). Replace `T_i, T_{i+1}` by `(T_i, T_{i+1})`, keeping pointer `i`. Then
     `E(x) o s_1` agrees with `E(x)` on `t <= 0`, and is `E(x)(t+1)` on `t >= 1`. On `[0,1]` it is
     `E(x)(2t)`, which is `a_i + h_{(T_i,T_{i+1})}(t)` by the recursion for `h`. This is exactly
     `E(merged)`.
   - *Pointer left* and *split* are the inverse moves, with `s_0^{-1}`, `s_1^{-1}`.

   So every move `x -> y` by generator `g` satisfies `E(y) = g E(x)` in `G`: it is a Cayley edge.
   - *Membership in G.* The all-leaves state with pointer `0` has `E = id`, and every state is
     reached from it by moves inside `S_n`, so `E(S_n) ⊂ G`.
   - *Injectivity.* `E` determines the state.
     - The values `E(k)`, `k in Z`, give the block partition, and `E(0)` marks the pointer block.
     - The blocks inside `[0, n]` are the window trees, since the outside leaves sit at fixed places.
     - On each block, the preimages of the integers under `h_T` form the dyadic leaf partition of
       `T`, which determines `T`.

   `model_check.py` confirms all of this in exact arithmetic for `n <= 9`: every move is the stated
   Cayley edge, and `E` is injective on `S_n` (`model_check.out`, 11934 states at `n = 9`).

3. **Rayleigh bound.** Let `f >= 0` be supported on `E(S_n)`. From a state there is at most one
   move per generator, so the directed move edges form a subset of the pairs `(x, g)`. Hence
   `<f, K f> >= Num_n := sum over directed moves x -> y of f(x) f(y)`. Also `<f,f> = D_n :=
   sum_{S_n} f^2`, by injectivity. So `||K|| >= Num_n / D_n`.

4. **Test vector.** Fix a truncation `N`, positive dyadic rationals `phi(l,r)`, `g(l,r)`
   (`l, r >= 1`, `l + r <= N`), `x_1`, `y_1`, and positive dyadic scalars `rho`, `tau`.
   - *Raw weights.* `x_raw(leaf) = x_1`, `x_raw((L,R)) = phi(|L|,|R|) x_raw(L) x_raw(R)`;
     `y_raw(leaf) = y_1`, `y_raw((L,R)) = g(|L|,|R|) y_raw(L) x_raw(R)`. Both are `0` on trees with
     more than `N` leaves.
   - *The vector.* `f(T_0..T_{m-1}; i) = tau y_raw(T_i) prod_{j != i} rho x_raw(T_j) >= 0`, put on
     `E(state)`.
   - *Shape sums over trees with `s` leaves.* `A_s = sum x_raw^2`, `Bq_s = sum y_raw^2`,
     `X_s = sum x_raw y_raw`, and `M_{k,l} = g(k,l) Bq_k A_l`. The recursions in `exact_sums` follow
     by splitting `T = (L, R)`; for example, `Bq_s = sum_{l+r=s} g(l,r)^2 Bq_l A_r`.

5. **Renewal identity.**
   - *Scaled sums.* `p_s = rho^2 A_s`, `q_s = tau^2 Bq_s`, `B_s = rho X_s`.
   - *Renewal.* `Z_0 = 1`, `Z_m = sum_s p_s Z_{m-s}`. Then `Z_l` is the sum, over sequences of trees
     with `l` leaves in total, of `prod (rho x_raw)^2`.
   - *Norm.* Split a state into the left sequence (`l` leaves), the pointer tree (`s`) and the right
     sequence. This gives `D_n = sum_{l+s+r=n} Z_l q_s Z_r = sum_l Z_l W_{n-l}`, with `W = q * Z`.
   - *Edges.* They pair up as (pointer right, pointer left) and (merge, split), each pair a
     reversal, so `Num_n` is twice the sum over pointer-right and merge edges. Let `S = T_i`
     (`s` or `k` leaves) and `U = T_{i+1}` (`t` or `l` leaves). The two factors share all other
     trees, and `rest = prod_{j != i,i+1} (rho x_raw(T_j))^2`, which sums to `Z_l Z_r`. With
     `tau = 1` the identity is what the self-test checks; `tau` only rescales `f`, `Num_n` and
     `D_n` by `tau`, `tau^2`, `tau^2`.
     - Pointer right: `f(x) f(y) = [tau y_raw(S) rho x_raw(S)] [rho x_raw(U) tau y_raw(U)] * rest`.
       Summed over shapes, this gives `tau^2 B_s B_t` per pair of sizes.
     - Merge: `f(x) f(y) = tau y_raw(S) rho x_raw(U) * tau g(k,l) y_raw(S) x_raw(U) * rest`.
       Summed over shapes, this gives `tau^2 rho M_{k,l}`, and it is nonzero only if `k + l <= N`,
       as the truncation requires.
     - Hence `Num_n = 2 sum_{l+j+r=n} Z_l H_j Z_r = 2 sum_l Z_l V_{n-l}`, with `V = H * Z` and
       `H_j = tau^2 (sum_{s+t=j} B_s B_t + rho sum_{k+l=j} M_{k,l})`.
   - *Checks.* `certify_window.py test` verifies the identity against brute-force enumeration of
     `S_n` with the move generator of `model_check.py`, for `n = 2..7`, random dyadic parameters and
     `N = 4`. The two agree exactly as Fractions.

6. **Outward rounding.** Every quantity in step 5 is a finite sum of products of nonnegative
   rationals. `bounds(..., up=False)` evaluates `Num_n` in fixed point `2^-160`, rounding every input
   and every partial result down; `up=True` evaluates `D_n` rounding up. Addition and multiplication
   are monotone on nonnegatives, so `Num_lo <= Num_n` and `D_hi >= D_n`, and
   `||K|| >= Num_lo / D_hi`. The self-test also asserts `Num_lo/D_hi <= Num_n/D_n` exactly.

7. **The instance.**
   - *Parameters.* `N = 80`, `n = 30000`. `phi, g, x_1, y_1` are the `2^-24`-rounded output of the
     float optimiser `split_ansatz.py`, stored as integers in `params_N80.json`. Their provenance
     does not matter for validity. `rho` and `tau^2` are the `2^-40`-dyadic roundings in
     `certificate`.
   - *Result.* `python3 certify_window.py params_N80.json 80 30000` uses pure Python (`fractions`
     and integers only). It prints `||K|| >= a/b` with the `a, b` of the claim, recorded in
     `certify_N80_n30000_json.out` and `certificate_N80_n30000.json`.
   - *The final inequality* `a/(4b) > 9397/10000` is checked exactly as Fractions.

   Hence `||P|| = ||K||/4 > 0.9397`.

   The same command on `params_N40.json 40 20000` gives the second instance, `||P|| > 0.9287`.
