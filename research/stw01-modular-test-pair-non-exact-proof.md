---
rg: 2
id: stw01-modular-test-pair-non-exact-proof
kind: route
title: Dilate inside Q and use that quotients of exact algebras are exact
target: stw01-modular-test-pair-generates-non-exact-algebra
requires: []
---

1. **Dilate inside `Q`.** Take `a = lambda_1 e_1 + lambda_2 e_2 + lambda_3 e_3 in Q` with
   distinct `lambda_i in (0, 1)`, `m = min_i lambda_i (1 - lambda_i)` and `b = m p <= a - a^2`.
   The three-block dilation of the modular artifact (Step 4', which needs only an
   invertible `a` with `a - a^2 >= m 1`) gives a projection `r = c a^(-1) c*` in `M_3(Q)`,
   with `c = (a, b^(1/2), (a - a^2 - b)^(1/2))^T`. It satisfies
   `f_1 r f_1 = a (+) 0 (+) 0` and `f_1 r f_2 r f_1 = m p (+) 0 (+) 0`.
2. **Map `Q` into `M_3(Q)`.** The universal property of the unital full free product
   gives a *-homomorphism `pi : Q -> M_3(Q)` with `e_j -> f_j` and `p -> r`. Then
   `pi(h) = a (+) 0 (+) 0` and `pi(k) = m p (+) 0 (+) 0`, so
   `pi(C*(h, k)) = C*(a, p) (+) 0 (+) 0`.
3. **Identify the image.** `sp(a) = {lambda_1, lambda_2, lambda_3}` avoids `0`, so `C*(a)`
   contains `1` and every spectral projection `e_i`. Hence
   `C*(a, p) = C*(1, e_1, e_2, e_3, p) = Q`, and `C*(h, k)` surjects onto a copy of `Q`.
4. **`Q` is not exact.** `PSL_2(Z)` contains a free group of rank 2, the full group
   C*-algebra of a subgroup of a discrete group embeds in that of the group, and
   `C*(F_2)` is not exact (Wassermann). Exactness passes to C*-subalgebras.
5. **Conclude.** Exactness passes to quotients (Kirchberg), so `C*(h, k)` is not exact. ∎
