---
rg: 2
id: inner-realizer-length-radius-proof
kind: route
title: A short realizer word makes a nontrivial kernel commutator close up at most realized points, which the sofic radius forbids
target: inner-realizers-are-at-least-half-the-sofic-radius
requires:
  - kun-expander-decomposition-formalized
---

Notation as in the target. Permutations act on the left. For a word
`u = t_1 ... t_m` in `S`, `u(s~)` is the product `t_1~ ... t_m~`.

1. **The error set is small.** For a fixed word `u`, `u(s~)` agrees with
   `u(sigma_n(S))` off `|u|` times the number of edited points, and
   `u(sigma_n(S))` agrees with `sigma_n(u)` off `o(|X_n|)` points by almost
   multiplicativity. Also `sigma_n(g) sigma_n(s) sigma_n(g)^-1` agrees with
   `sigma_n(g s g^-1)` off `o(|X_n|)` points, and `sigma_n(s) = s~` off
   `o(|X_n|)` points. With finitely many `s`, `|E_n| = o(|X_n|)`.
2. **A nontrivial commutator word.** Let `B` be `(w, eps)`-realized, with
   `c in C_B` and agreement set `A ⊂ B`, `|B \ A| <= eps|B|`. As elements of
   `G`, `w in N` and `g not in N`, so `h = w^-1 g != 1`. As `C_G(N) = 1` and `S`
   generates `N`, some `s in S` has `[h, s] != 1`. The word
   `d = w^-1 v_s w s^-1` has length at most `2|w| + L_g + 1` and represents
   `h s h^-1 s^-1 = [h, s] != 1` in `N`.
3. **The commutator word fixes most of the block.** Put `W = w(s_B)`, a
   permutation of `B`. For `x in B` let `y = W s_B^-1 x` and `a = (W c)^-1 y`.
   Suppose
   - `y` is not in `E_n`;
   - `a in A`, so `sigma_n(g) a = W c a = y` and `sigma_n(g)^-1 y = a`;
   - `s_B a in A`, so `sigma_n(g) s_B a = W c s_B a = W s_B c a = W s_B W^-1 y`,
     using that `c` commutes with `s_B`.

   Then `v_s(s~) y = sigma_n(g) s~ sigma_n(g)^-1 y = W s_B W^-1 y`, and

   ```text
   d(s~) x  =  W^-1 v_s(s~) W s_B^-1 x  =  W^-1 v_s(s~) y  =  s_B W^-1 y  =  x .
   ```

   The maps `x -> y` and `y -> a` are bijections of `B`. The three conditions
   fail for at most `e_B`, `eps|B|` and `eps|B|` values respectively. So `d(s~)`
   fixes at least `(1 - 2 eps)|B| - e_B` points of `B`.
4. **Fixed points have small radius.** If `d(s~) x = x`, the word `u = d` and the
   empty word `u'` satisfy `u(s~) x = u'(s~) x` while `u != u'` in `N`. So
   `rho_n(x) < |d| <= 2|w| + L_g + 1`.
5. **Summation, and the per-block form.** If `|w_B| <= l`, step 4 puts every
   fixed point of step 3 into `{rho_n < 2l + L_g + 1}`. Summing step 3 over the
   realized blocks gives the inequality. For one block, suppose more than
   `2 eps|B| + e_B` points have `rho_n >= r` and `|w| < (r - L_g - 1)/2`. Then
   fewer than `(1 - 2 eps)|B| - e_B` points have `rho_n < 2|w| + L_g + 1`,
   against steps 3 and 4.
6. **Fixed radius.** `rho_n(x) < r` means that some pair of words of length at
   most `r` violates the defining equivalence at `x`, and there are finitely many
   pairs.
   - If `u != u'` in `N`, then `u(s~) x = u'(s~) x` forces, off `o(|X_n|)`
     points, `sigma_n(u'^-1 u) x = x`, and `sigma_n(u'^-1 u)` has `o(|X_n|)`
     fixed points.
   - If `u = u'` in `N`, then `u(s~)` and `u'(s~)` agree off `o(|X_n|)` points.

   So `|{rho_n < r}| = o(|X_n|)` along `U`. ∎
