---
rg: 2
id: finite-subgroup-induced-absorption-conserves-entropy-proof
kind: route
title: Apply the additive lifted p-adic trace to both sides of the module isomorphism
target: finite-subgroup-induced-absorption-conserves-entropy
requires:
  - lifted-trace-detects-finite-subgroup-projectives
---

Let `t_p: K_0(F_p[G]) -> Z_p` be the lifted trace of `lifted-trace-detects-finite-subgroup-projectives`.
It is additive and depends only on isomorphism classes.

1. **Induced modules.** A finitely generated projective `F_p[F]`-module `Q` is `e F_p[F]^k` for an idempotent
   matrix `e` over `F_p[F]`. So `Ind(Q) = e F_p[G]^k`, the module named in (LFT1), up to the left/right
   convention used there, which changes nothing. (LFT1) gives `t_p([Ind(Q)]) = dim(Q)/|F| = rho(F, Q)`.
   For `F = 1` and `Q = F_p`, `t_p([F_p[G]]) = 1`.
2. **Both sides.** Additivity gives `t_p(LHS) = m + sum_i rho(F_i, Q_i)` and
   `t_p(RHS) = m + sum_j rho(F'_j, Q'_j)`. The modules are isomorphic, so the values agree in `Z_p`.
3. **Rational equality.** The two sums are rational numbers lying in `Z_p ⊆ Q_p`. `Q` embeds in `Q_p`, so they
   are equal as rational numbers.
4. **Item 1 of the target.** If `F_p[G]^n ≅ F_p[G]^n ⊕ ⊕_i Ind(Q_i)`, step 3 gives `sum_i dim(Q_i)/|F_i| = 0`.
   Each term is nonnegative, so every `Q_i = 0`. Projectivity is automatic here: a direct summand of a free
   module is projective, and `Q_i` is a direct summand of the restriction of `Ind(Q_i)` to `F_i` (the
   double coset `F_i · 1 · F_i`). So the hypothesis of
   `induced-projective-absorption-breaks-bernoulli-classification` cannot hold.
5. **Item 2 of the target.** Corollary D of `coinduced-finite-subgroup-shifts-add-entropy-to-bernoulli`
   identifies `(F_p^m)^G × prod Coind(X_(Q_i))` with a Bernoulli shift of base entropy
   `m log p + sum_i rho(F_i, Q_i) log p`, when `m >= 1`. By step 3 the two sides give the same base entropy.

**The route it kills.** `leavitt-induced-absorption-gives-bernoulli-collapse` consumed an induced absorption
over the binary Leavitt units. Step 4 shows no group has one.
