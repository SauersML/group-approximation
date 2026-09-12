---
rg: 2
id: covariant-monotone-cylinder-families-constant-proof
kind: route
title: Transitivity gives one rank, faithfulness turns inclusions into equalities, and one prefix replacement joins the two letters
target: covariant-monotone-cylinder-families-in-rank-models-are-constant
requires: [binary-leavitt-unit-group-is-simple]
artifacts:
  - research/artifacts/covariant-diagonal-plan-adversarial-audit-2026-09-12.md
---

Proof, artifact Sections 1–3.

1. **Joins.**
   - **Existence.** The finite joins `f_n M` increase, with rank tending to `s`. An idempotent `e` with
     `e f_n = f_n` for all `n` and `rk e <= s` realizes a finitely satisfiable countable type, so it
     exists by countable saturation.
   - **Leastness.** Faithfulness of rank on principal right ideals gives it.
   - **Meets.** The same argument with the inclusions reversed.
2. **Rigidity.**
   - **One rank.** `V` is transitive on proper cylinders, so `rk A_w` is constant.
   - **Equalities.** `A_(wi) ⊆ A_w` with equal rank gives `A_(wi) = A_w`. So `A` is constant on
     cylinders beginning with `0`, and on those beginning with `1`.
   - **Joining the letters.** The leaf map `(00, 01, 1) -> (00, 1, 01)` gives
     `A_[0] = sigma(v) A_[00] = sigma(v) A_[01] = A_[1]`.
   - **Orthogonal idempotents.** For covariant orthogonal `e_w`, `e_(w0) M = e_(w1) M`, so
     `e_(w0) = e_(w0) e_(w1) m = 0`.
3. **Root spans.**
   - **Coincidence.** `v s_w y t_(w') v^-1 = s_(vw) y t_(vw')`, `s_(w0) y t_(w') = s_w (s_0 y) t_(w')` and
     `s_w y t_(w'0) = s_w (y t_0) t_(w')` make the spans covariant and monotone in both slots, with one
     common rank. So refined spans coincide.
   - **Frame identity.** `L_(b,a1) V_(a0,b) = 0` gives `N_(b,a)(y) N_(a,b)(z) = 0`, and the swap of `a`
     and `b` gives the reversed products.
   - **Weyl element.** With `X = N_(a,b)(1)` and `Y = N_(b,a)(1)`, `sigma(w) X = Y sigma(w)` reads
     `X + X^3 = Y + Y^2`. This gives `X^2 = 0`, then `Y^2 = 0`, then `X = Y`.
   - **Triviality.** `sigma(j([[0,1],[1,1]])) = 1`, and `R^x` is simple, so `sigma` is trivial.
