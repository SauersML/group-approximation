---
rg: 2
id: liftable-abelian-subalgebras-are-amplification-invariant-proof
kind: route
title: Dilate the POVM, round the dilated projection to a block-diagonal one of the right rank, and compress back by a polar part
target: liftable-abelian-subalgebras-are-amplification-invariant
requires: []
---

## Lemma 1

Put `H = C^k`, `K = C^k (x) C^F`, `E_A = 1 (x) |A><A|`, and `Vxi = sum_A a_A^(1/2) xi (x) |A>`. For operators
between `H` and `K` use `||X||'_2^2 = Tr(X^* X)/k`, which is the normalized 2-norm on `H`. Two facts are
used repeatedly: `sum_A ||X E_A||'^2 = ||X||'^2`, and `||X E_A Y||'_2 <= ||X E_A||'_2 ||Y||`.

1. **Dilation.** `V^* V = sum_A a_A = 1` and `V^* E_A V = a_A`. Put `Pi = V V^*`, a projection with `Tr Pi = k`.
2. **Pi almost commutes with the E_A.** `Tr(V^* E_A (1 - Pi) E_A V) = Tr(a_A - a_A^2)`, so
   `sum_A ||(1 - Pi) E_A Pi||'^2 = gamma`. Since `[E_A, Pi] = (1 - Pi) E_A Pi - Pi E_A (1 - Pi)` with orthogonal
   terms, `sum_A ||[E_A, Pi]||'^2 = 2 gamma`.
3. **Diagonal part.** `Pi_D = sum_A E_A Pi E_A`. Then `||Pi - Pi_D||'^2 = sum_A ||E_A Pi (1 - E_A)||'^2`, and
   `E_A Pi (1 - E_A) = -E_A [Pi, E_A] (1 - E_A)`, so `||Pi - Pi_D||'^2 <= 2 gamma`.
4. **Rounding the blocks.** `b_A = E_A Pi E_A` has `tau'(b_A - b_A^2) = ||(1 - E_A) Pi E_A||'^2`, summing to
   at most `2 gamma`. Let `p'_A = chi_(1/2,1](b_A) <= E_A`. For `t in [0,1]`, `|t - chi(t > 1/2)|^2 <= t(1-t)`,
   so `sum_A ||b_A - p'_A||'^2 <= 2 gamma`. `Pi' = sum_A p'_A` is a projection commuting with every `E_A`, and
   `||Pi - Pi'||'^2 <= 2 ||Pi - Pi_D||'^2 + 2 ||Pi_D - Pi'||'^2 <= 8 gamma`.
5. **Rank.** Put `u = Tr|Pi' - Pi| / k`. The support of `Pi' - Pi` lies under `Pi v Pi'`, of normalized trace
   at most `2 + u`. By Cauchy--Schwarz, `u <= (2 + u)^(1/2) (8 gamma)^(1/2)`, so `u <= 8 gamma + 4 gamma^(1/2)`.
   Enlarge or shrink the `p'_A` inside their `E_A` by subprojections of total normalized rank
   `|Tr Pi' - k| / k <= u`. The result `Pi''` commutes with every `E_A`, has `Tr Pi'' = k`, and
   `||Pi - Pi''||'^2 <= 16 gamma + 2u <= 32 gamma + 8 gamma^(1/2) =: eta`.
6. **Compressing back.** `W_0 = Pi'' V` has `||W_0 - V||'_2 = ||(1 - Pi'') Pi||'_2 <= eta^(1/2)`. Its polar part
   maps into `ran Pi''`, and `dim ran Pi'' = k`, so it extends to a unitary `U : H -> ran Pi''` with `W_0 = U |W_0|`.
   Since `0 <= |W_0| <= 1`, `||U - W_0||'_2 = ||1 - |W_0| ||_2 <= ||1 - |W_0|^2||_2 = ||V^* (1 - Pi'') V||_2 <= eta^(1/2)`.
   So `||U - V||'_2 <= 2 eta^(1/2)`.
7. **The partition.** `Pi''` commutes with `E_A`, so `p_A = U^* E_A U` are projections on `H` with
   `sum_A p_A = U^* Pi'' U = 1`. Since `a_A - p_A = (V - U)^* E_A V + U^* E_A (V - U)`,

   ```text
   sum_A ||a_A - p_A||_2^2  <=  2 ||V - U||'^2 + 2 ||V - U||'^2  <=  16 eta  =  512 gamma + 128 gamma^(1/2) .  ∎
   ```

## Lemma 2

The direction `D` liftable implies `1 (x) D` liftable is immediate: use `1 (x) C_n`. For the converse let
`{q_A}` span `C~_n`, and let `E(x) = 1 (x) (tau_N (x) id)(x)`, the trace-preserving conditional expectation
onto `1 (x) M_(k_n)` given by the normalized partial trace over `M_(N_n)`. Put `a_A = (tau_N (x) id)(q_A)`.

1. **Random signs.** For signs `c_A` and `g = sum_A c_A q_A`, the mean of `||[u, g]||_2^2` over independent
   uniform signs is `sum_A ||[u, q_A]||_2^2`, for any unitary `u`.
2. **Blocks are nearly in `1 (x) M_k`.** Every element of `C = 1 (x) D` commutes with `prod_U (M_N (x) 1)`. By
   step 1, `sum_A ||[u (x) 1, q_A]||_2^2 -> 0` along `U`, uniformly over `u in U(N_n)`: otherwise pick violating
   `u_n` and signs. Averaging over Haar `u` gives `E(q) = int (u (x) 1) q (u (x) 1)^* du`, so by convexity
   `gamma_n = sum_A ||q_A - 1 (x) a_A||_2^2 -> 0`.
3. **The POVM.** `sum_A a_A = 1`, and Pythagoras gives `||q_A - E q_A||_2^2 = tau(q_A) - ||E q_A||_2^2 = tau(a_A - a_A^2)`.
   So `gamma_n = sum_A tau(a_A - a_A^2)`. Lemma 1 gives partitions `{p_A}` of `M_(k_n)` with
   `beta_n = sum_A ||a_A - p_A||_2^2 <= 640 gamma_n^(1/2) -> 0`.
4. **Same algebra.** Fix coefficients `|c_A| <= 1`.
   - `||sum_A c_A (q_A - 1 (x) a_A)||_2 = ||(1 - E) g||_2 -> 0`, uniformly over the unit ball of `C~_n`:
     otherwise a violating sequence gives an element of `1 (x) D` at positive distance from `1 (x) prod_U M_k`.
   - Put `x_A = a_A - p_A` and split `sum_A c_A x_A = sum_A c_A p_A x_A + sum_A c_A (1 - p_A) a_A`. The first sum
     has orthogonal left supports, so its squared norm is at most `beta_n`.
   - For `0 <= c_A <= 1`, `sum_A c_A (1 - p_A) a_A = sum_B p_B y_B` with `0 <= y_B = sum_(A != B) c_A a_A <= 1 - a_B`.
     So `||p_B y_B||_2^2 <= tau(p_B y_B p_B) <= tau(p_B (p_B - a_B)) <= ||p_B||_2 ||x_B||_2`. Summing with
     Cauchy--Schwarz gives at most `beta_n^(1/2)`. General `c_A` split into four such parts.
   - Hence `||sum_A c_A q_A - 1 (x) sum_A c_A p_A||_2 -> 0` uniformly.
5. **Conclusion.** `C = prod_U C~_n` and `1 (x) prod_U span{p_A}` have the same elements, so
   `D = prod_U span{p_A}`.
6. **Masas.** `1 (x) Q` and `Q` are isomorphic, so the masas of `1 (x) Q` are `1 (x) D` for masas `D` of `Q`,
   and step 5 transfers liftability in both directions. ∎
