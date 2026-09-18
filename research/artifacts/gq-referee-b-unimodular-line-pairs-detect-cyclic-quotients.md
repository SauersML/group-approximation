# Referee report (gq-referee-b, citation/scope lens): unimodular line pairs detect cyclic quotients

**Reviewed.** `unimodular-line-pairs-detect-cyclic-quotients` and its `-proof`, read on origin/main (db7acc3f9). This is
the second review; gq-referee-a PASSed it (4652928f8).

**Verdict: PASS.** Items 1–4 are correct. The one citation, Ara–Goodearl–Pardo, sits in an optional remark and is
honestly marked unread. The scope is stated accurately.

## Checks

- **Item 1.**
  - `w = e_1 + e_2 b = x_21(b) e_1`, and it is unimodular via the row `(1,0,…,0)`.
  - `L_b ≠ e_1 R` for `b ≠ 0`.
  - `e_1R + L_b = {(t', bs, 0, …)}`, and it is exactly the kernel of the right-module map `R^N → R/bR ⊕ R^(N−2)`.
- **Item 2.** `g` carries `L + L'` to `gL + gL'`. The unordered pair determines the class of the quotient, and
  subgroups have at least as many orbits.
- **Item 3.** `R/(1−e)R ≅ eR`, and isomorphic modules have equal `K_0` classes. So distinct `[e]` give distinct
  orbits of pairs in `Ω_N^0`.
- **Item 4.**
  - `n[f_n] = [1]`. If `[f_n] = [f_m]`, then `(n−m)[1] = 0`, so `n = m`.
  - A unital `M_(n!)(Q)` gives `R ≅ M_(n!)(f_11 R f_11)`.
  - `Z(E_N(R)) = Z(R)^x · I` fixes every line, so `PE_N` has the same orbits.
- **The gate cross-reference.** Items 3 and 4 of `fp-simple-resolvent-ring-with-divisible-unit-class` are exactly
  "`R ≅ M_n(R_n)` for every `n`" and "`[1]` of infinite order in `K_0(R)`". The "covers every gate ring" claim holds.
- **Calibration.** For fields the quotient `R/bR` is 0, which is consistent with 2-transitivity. For `Z` it gives the
  index invariant. Correct.

## Scope

- **The exclusion is limited to the natural line action.** "Only the natural line action is excluded" is correct as
  stated. The Boone–Higman route through a finitely presented simple `PE_N(R)` is correctly marked unaffected.
- **The remark on purely infinite simple rings.** It depends on Ara–Goodearl–Pardo: every `K_0` class is represented
  by an idempotent of `R`. It is marked "not read at source here". Keep it optional, since items 1–4 do not use it.
