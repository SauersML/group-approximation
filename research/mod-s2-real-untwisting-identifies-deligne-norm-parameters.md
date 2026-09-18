---
rg: 2
id: mod-s2-real-untwisting-identifies-deligne-norm-parameters
kind: claim
title: The universal-cover cocycle of Sp4(Z) is a unique real coboundary on Mod(S_2), so every point-norm Maslov parameter is a point-norm separating-twist scalar of Mod(S_2) and conversely
distinct_from:
  deligne-triple-cover-is-a-torelli-scalar-quotient-of-mod-s2: that splits the mod-three pullback with Z/3 coefficients and treats the single parameter 1/3; this trivializes the integral cocycle with real coefficients and transports the whole point-norm parameter group P_op, at every theta, to asymptotic homomorphisms of Mod(S_2).
  deligne-torelli-character-counts-separating-twists: its (ST4) is the normalized-HS almost-representation dictionary at the cube roots; this is an operator-norm dictionary for all parameters, with the exact scalar exponent -r*theta.
  mod-s2-exact-models-are-fd-character-limits-of-deligne-sectors: that concerns exact representations and normalized-HS distance; this concerns operator-norm asymptotic homomorphisms.
  deligne-sep7-norm-parameter-closed-subgroup: that defines P_op and proves it is a closed subgroup; this identifies it with a closed subgroup Z_op of Mod(S_2) data.
---

**ESTABLISHED** through `mod-s2-real-untwisting-deligne-norm-parameters-proof`. Unreviewed; no
novelty claimed.

**Setting.**
- `M = Mod(S_2)`, `pi : M -> Gamma = Sp_4(Z)`, `K = ker pi` the Torelli group, `t_s` a separating twist.
- `b` is the normalized integral cocycle of the universal-cover extension of `Gamma`, `c_theta = exp(2 pi i theta b)`, and `P_op`
  is the point-norm parameter group, all exactly as in `deligne-sep7-norm-parameter-closed-subgroup`.
- `Z_op` is the set of `alpha in R/Z` for which there are `d_n` and maps `V_n : M -> U(d_n)` with
  `V_n(e) = I`, `||V_n(m)V_n(m') - V_n(mm')||_op -> 0` for all fixed `m, m'`, and
  `||V_n(t_s) - exp(2 pi i alpha) I||_op -> 0`.
  It does not depend on `s` (separating twists are conjugate, (ST1)).

**Statement.**

1. **(U1) Untwisting function.** There is a unique `f : M -> R` with
   `f(m) + f(m') - f(mm') = b(pi m, pi m')` for all `m, m'`. It satisfies:
   - `f(e) = 0`;
   - `f|_K` is a conjugation-invariant homomorphism;
   - `f(t_s) = r` is the same for every separating twist;
   - `r = a/10` with `a` an integer and `3` not dividing `a`; in particular `r != 0`;
   - `sigma = f|_K / r` is an integer-valued homomorphism `K -> Z` equal to `1` on every separating twist;
   - `exp(2 pi i f)` is a character of `M`, so `+-r mod 1` lie in `Z_op`.
2. **(U2)** `Z_op` is a closed subgroup of `R/Z`.
3. **(U3) Dictionary.** For every real `theta`: `theta mod 1` lies in `P_op` iff `-r theta mod 1` lies in `Z_op`.
   Explicitly, `V_n = exp(-2 pi i theta f) (U_n o pi)` and `U_n(g) = exp(2 pi i theta f(s(g))) V_n(s(g))` for any
   section `s` with `s(e) = e`. Operator-norm defects agree pair by pair in the first direction.
4. **(U4) Consequences.**
   - `1/3` lies in `P_op` iff `1/3` lies in `Z_op`. So the exact radical `Rad_MF(E_3) = C_3`, which is equivalent to
     `1/3 notin P_op`, is equivalent to: **no point-norm asymptotic homomorphism of `Mod(S_2)` sends a separating twist to
     a primitive cube-root scalar.**
   - `P_op = R/Z` iff `Z_op = R/Z`. `P_op` is finite iff `Z_op` is finite.

**Reading.** On `Sp_4(Z)` the Maslov class is rationally nonzero (Dadarlat windings live there). After pulling back to
`Mod(S_2)` it is a real coboundary, because `H^2(Mod(S_2); R) = 0`. So every twisted model becomes an untwisted
asymptotic homomorphism, and the only surviving datum is the scalar reached by one separating twist. This is the
operator-norm, all-parameter form of the one-word dictionary (ST4).
