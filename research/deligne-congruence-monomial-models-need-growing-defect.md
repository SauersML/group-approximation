---
rg: 2
id: deligne-congruence-monomial-models-need-growing-defect
kind: claim
title: Monomial sector models of a Deligne cover over Sp_2g(Z)/Gamma(p) with zeta of prime order q >= 7 and p^4 != 1 mod q have at least c_g p^(2g^2+g-10) defective cells
distinct_from:
  deligne-bounded-rank-monomial-models-need-large-detecting-cycles: that proves [Gamma:N] <= m A for a detecting cycle of mass A and shows alpha(N) stays bounded along towers, leaving open whether alpha -> 0 along congruence quotients; this constructs detecting cycles of mass |Sp_4(F_p)| A on Y_(Gamma/Gamma(p)), so alpha(Gamma(p)) -> 0 and the defective-cell count grows polynomially in p.
  deligne-monomial-cover-models-have-a-detecting-cycle-floor: that gives the normalized HS floor 4 nu / A for any detecting cycle and the systole lower bound on A_0; this is an upper bound on A_0(Gamma(p)) obtained by transfer from a Deligne-residual Sp_4 block.
  deligne-cover-bounded-rank-sector-tuples-have-bounded-dimension: that is the bounded-rank rung for all unitary tuples; this kills only the monomial class over prime-level principal congruence quotients.
---

**ESTABLISHED** (`deligne-congruence-monomial-models-need-growing-defect-proof`). Unreviewed.

**Setting.** Use the notation of `deligne-monomial-cover-models-have-a-detecting-cycle-floor`:
- `Gamma = Sp_(2g)(Z)` with `g >= 3`, presented as `<S | R>`, with the lifted presentation `r~(S) = z^(k_r)` of the preimage `Gamma~` of `Gamma` in the universal cover of `Sp_(2g)(R)`.
- `Gamma_n = Gamma~ / <z^n>`.
- A monomial sector model over a finite `Gamma`-set `X` has `rho(z) = zeta I` and `rho(s) = D_s P_s`. Its number of defective cells is `m`.
- `Y_X` is the Schreier 2-complex.
- The **value** of an integral 2-cycle `Sigma = sum n_(x,r) (x,r)` is `kappa(Sigma) = sum n_(x,r) k_r`.

Let `H = Sp_4(Z)`, embedded as a symplectic block of `Gamma`.

**Theorem.**
1. **Block cycle.** There is an integral 2-cycle `Sigma_H` on `Y_(Gamma/H)` of finite mass `A` whose value `kappa_H` is not divisible by `q`. This holds for every prime `q >= 3`.
2. **Transfer bound.** Let `N` be a normal subgroup of finite index, put `Lambda = HN` and `D = [Lambda : N]`. If `q` does not divide `D`, then `Y_(Gamma/N)` carries a detecting cycle of mass at most `D A` for every `zeta` of order `q`. Every monomial sector model over `Gamma/N` with such a `zeta` has

   ```text
   m >= [Gamma : HN] / A.                                                   (BT)
   ```

3. **Principal congruence quotients.** Take `N = Gamma(p)`. Then `D = |Sp_4(F_p)| = p^4 (p^2-1)(p^4-1)`, which `q` does not divide exactly when `p != q` and `p^4 != 1 mod q`. Such primes exist in infinitely many residue classes when `q >= 7`, for example `q = 7` with `p = 2, 3, 5, 11, 17, ...`. For these `p`,

   ```text
   m >= |Sp_(2g)(F_p)| / (|Sp_4(F_p)| A) >= 2^(-(g-2)) p^(2g^2+g-10) / A,
   alpha(Gamma(p)) <= A / [Gamma : H Gamma(p)] -> 0.
   ```

**Consequences.**
- **Class kill.** Fix a rank `k`. A monomial sector model over `Gamma/Gamma(p)` whose relator defects have rank at most `k` has `m <= k |R|`. By (BT), for every `zeta` of prime order `q >= 7` dividing `n`, only finitely many admissible primes `p` (`p^4 != 1 mod q`) carry such a model. This answers the "sharp question" of `deligne-bounded-rank-monomial-models-need-large-detecting-cycles` for these levels: `alpha(Gamma(p)) -> 0`.
- **Quantitative.** The fraction of defective cells is at least `c/(A p^10)` of `d = |Sp_(2g)(F_p)|`, polynomial in `1/p` and independent of `g`.
- **Mechanism.** The detecting cycle comes from a subgroup `H` that has its own Deligne residual and a small mod-`p` image. Transferring from `HN` instead of from `Gamma` replaces the bounded transfer ratio by `1/[Gamma : HN]`.

**Limits.**
- For `q = 3` and `q = 5`, `|Sp_4(F_p)|` is divisible by `q` for every `p`, and the transferred value vanishes mod `q`. Principal congruence quotients for `zeta` of order 3 or 5 stay open. Minimal detecting cycles need not be transfers.
- A smaller block cannot help. The preimage of `SL_2(Z)` maps onto `Z` (it is the braid group `B_3`), so it has characters with `z -> zeta`, and there is no detecting cycle on its presentation complex.
- The count uses the deck group of `Gamma/N` and scalar holonomy. General unitary tuples are untouched, so the rung remains open.
- The Deligne covers relevant to the sector route may take any `n >= 3`, so `n = 7` puts the whole route inside the killed range.

## Attempts

- 2026-09-17 sw-021: proof by Deligne residual for the `Sp_4(Z)` block, a character argument (`H^2(K;R/Z) = Hom(H_2, R/Z)`), and transfer along `Y_(Gamma/N) -> Y_(Gamma/HN)`. Numerical check: `q` does not divide `|Sp_4(F_p)|` for `q = 7`, `p in {2,3,5,11,17,19,23,31,37}`, and never for `q = 3, 5` among `p <= 43`.
