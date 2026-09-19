---
rg: 2
id: thompson-t-mf-iff-opnorm-z4-z3-defect-gap-vanishes
kind: claim
title: Thompson's T is MF iff nontrivial irreducible unitary pairs (A,B) with A^4 = B^3 = 1 have arbitrarily small operator-norm defect on the three long Lochak--Schneps relators
distinct_from:
  thompson-v-mf-iff-opnorm-s4-s3-defect-gap-vanishes: that is the criterion for V over the amalgam S4 *_Z2 S3, which needs an alignment of the two copies of the amalgamated involution; this is the criterion for T over the free product Z/4 * Z/3 of cyclic groups, where each generator is corrected separately by spectral rounding and no alignment exists.
  thompson-t-has-full-mf-radical: that is the target statement; this reformulates it as a uniform lower bound on the defect of nontrivial irreducible exact pairs, and its sufficiency half needs no presentation of T and no simplicity.
  mf-radical-words-have-linear-certificates: that is a general linear-certificate criterion over arbitrary unitary tuples; this replaces arbitrary tuples by exact pairs of finite-order unitaries and the linear bound by one positive gap.
artifacts:
  - experiments/thompson-t-opnorm-defect-gap-2026-09-17/verify_ls.py
  - experiments/thompson-t-opnorm-defect-gap-2026-09-17/find_words.py
  - experiments/thompson-t-opnorm-defect-gap-2026-09-17/out_verify_ls.json
  - experiments/thompson-t-opnorm-defect-gap-2026-09-17/out_find_words.json
---

**ESTABLISHED** by `thompson-t-mf-iff-opnorm-z4-z3-defect-gap-proof` (written proof).

## Setting

Use the generators and relators of `thompson-t-lochak-schneps-presentation`:

```text
G0 = Z/4 * Z/3 = < alpha, beta | alpha^4, beta^3 >,     T = G0 / << r_1, r_2, r_P >>,
r_1 = [bab, a^2 bab a^2],   r_2 = [bab, a^2 b^2 a^2 bab a^2 b a^2],   r_P = (ba)^5    (a = alpha, b = beta).
```

A finite-dimensional unitary representation of `G0` is an arbitrary pair `(A, B)` of unitaries in `U(n)`
with `A^4 = B^3 = 1`. Put

```text
D(A,B) = max( ||r_1(A,B) - 1||, ||r_2(A,B) - 1||, ||r_P(A,B) - 1|| )      (operator norm),
delta_n = inf { D(A,B) : (A,B) in U(n)^2, A^4 = B^3 = 1, (A,B) != (1,1) }.
```

Call `(A, B)` a **delta-pair** if `A^4 = B^3 = 1` and `D(A,B) < delta`.

## Statement

1. **(Each dimension is gapped.)** For every `n`, `delta_n` is attained and `delta_n > 0`. Also
   `delta_(n+1) <= delta_n`, and `delta_1 = 2 sin(pi/12) = 0.5176...`.
2. **(Irreducible form.)** `delta_n` is the minimum of `D(sigma)` over nontrivial irreducible
   representations `sigma` of `G0` with `dim sigma <= n`, because `D(rho_1 (+) rho_2) = max D(rho_i)`.
3. **(Criterion.)** The following are equivalent:
   - `T` has full MF radical, that is, `T` is not MF;
   - there is `epsilon_0 > 0` such that every `epsilon_0`-pair is `(1, 1)`;
   - there is `epsilon_0 > 0` such that every nontrivial irreducible pair has `D >= epsilon_0`.

   **The gap implies full MF radical using only the verified half of the presentation**: the relators
   hold in `T`, and `alpha, beta` generate `T`. It needs neither completeness of the relator list nor
   simplicity. More precisely, if the gap holds then every homomorphism `T -> U_F` is trivial, for every
   filter model `U_F`.
4. **(Normal form.)** Up to conjugacy, `A` is a fixed diagonal matrix of fourth roots of unity and
   `B = Y B_0 Y^*`, with `B_0` a fixed diagonal matrix of cube roots of unity and `Y` in `U(n)`. So
   `delta_n` is a minimum over finitely many copies of the compact real-algebraic set `U(n)`.
5. **(Arithmetic form.)** For rational `q`, "`delta_n < q`" is decidable (Tarski--Seidenberg). "`T` is MF"
   is the Pi_2 sentence `forall k exists n : delta_n < 1/k`.

## What is new against V

- **No alignment step.** The corona-to-exact correction for `G0 = Z/4 * Z/3` rounds each generator's
  spectrum to the nearest root of unity. The bound is `||f(u) - u|| <= (pi/2k) ||u^k - 1||`, with no
  smallness hypothesis.
- **No finite-group stability input.** No `finite-group-opnorm-support-profile` and no involution
  alignment (L0b of the V proof) are used.
- **Every nontrivial exact pair is far from 1.** `||A - 1|| >= sqrt 2` or `||B - 1|| >= sqrt 3`, so
  nontriviality survives every limit.
- **Why the V routes fail here.** The finite-subgroup obstructions of `V` are unavailable, because finite
  subgroups of `T` are cyclic (`finite-subgroups-of-thompson-t-are-cyclic`). The Kazhdan routes are
  unavailable too, because `T` has the Haagerup property. The criterion shows what remains: a single
  uniform spectral gap for the three long words over the representation variety of a virtually free
  group. That variety is the space of pairs `(diag, Y diag Y^*)`.
- **Downstream.** `thompson-t-pentagon-winding-sandwich` extracts from this criterion a K-theoretic
  necessary condition, `thompson-t-pentagon-winding-rigidity`.
