# Referee report (gq-referee-a, proof-gap lens): unimodular line pairs detect cyclic quotients

**Reviewed:** `unimodular-line-pairs-detect-cyclic-quotients` and its `-proof` (lane gq-infinite-primes, 27c30bc22), read
on origin/main.

**Verdict: PASS.** Items 1–4 hold, and I found no gap. There are two nits. N1 removes the hypothesis in the `PE_N`
remark, which holds automatically.

## Checks
- **Item 1: the kernel computation (the author asked about this).**
  - `x_21(b)e_1` is the column `(1, b, 0, …)`, that is, `e_1 + e_2 b`. The row `(1,0,…,0)` shows it is unimodular.
  - `w ∈ e_1R` forces `b = 0`, so `L_b ≠ e_1R`.
  - Sum and kernel:
    - `e_1 t + w s = (t+s, bs, 0, …)`, so `e_1R + L_b = {(t', bs, 0, …)}`.
    - `(r_1, r_2, r_3, …) ↦ (r_2 + bR, r_3, …)` is a surjective homomorphism of right modules, since `bR` is a right
      ideal.
    - Its kernel is `{r_2 ∈ bR, r_3 = … = 0} = e_1R + L_b`. ✓
- **Item 2: the invariant.** `g` maps `L + L'` onto `gL + gL'`, which gives an isomorphism of quotients that is
  symmetric in `L, L'`. Subgroups have at least as many orbits. ✓
- **Item 3: the idempotent form.**
  - `R = eR ⊕ (1−e)R` gives `R/(1−e)R ≅ eR`, and `1 − e ≠ 0`.
  - `eR ⊕ R^(N−2)` is finitely generated projective, and isomorphic modules have equal classes. So distinct `[e]`
    give distinct orbits of pairs inside `Ω_N^0 ⊆ Ω_N(R)`.
  - Type (A) requires finitely many orbits of two-element subsets (item 4 of the definition in
    `type-a-action-gives-boone-higman-for-subgroups`). So the conclusion is exactly a failure of type (A). ✓
- **Item 4: distinctness (the author asked about this).**
  - The matrix units `e_(i1)` give `f_iR ≅ f_1R`, and `Σf_i = 1` gives `R ≅ (f_1R)^n`. So `n[f_n] = [1]`.
  - If `[f_n] = [f_m]`, then `(n−m)[f_n] = 0`, so `(n−m)[1] = n·(n−m)[f_n] = 0`, and `n = m`.
  - Infinitely many `n` give infinitely many classes, all with `f_n ≠ 1` for `n ≥ 2`.
  - Gate items 3 (`R ≅ M_n(R_n)` for every `n`) and 4 (`[1]` of infinite order) are exactly these hypotheses.
  - A unital `U_Q` gives unital `M_(n!)(Q)`, hence `R ≅ M_(n!)(f_11 R f_11)`. ✓
- **The `PE_N` remark (the author asked about this).** It is correct, and its hypothesis always holds (N1).
- **The calibrations.**
  - Over a field, `R/bR = 0`, which gives one orbit. This matches the 2-transitivity of `PGL_N(F)`.
  - Over `Z`, `Z/b` is the index invariant. ✓

## Nits
- **N1 (the `PE_N` remark).** "When it acts on lines" holds automatically. An element `g` of `E_N(R)` commuting with
  every `e_ij(r)`:
  - commutes with every `E_ij`, `i ≠ j`, so `g = cI`;
  - satisfies `cr = rc` for all `r`, so `c ∈ Z(R)^×`.

  So `Z(E_N(R))` consists of central scalar matrices, and `cI·vR = v·cR = vR`. Hence `PE_N(R)` always acts on
  `Ω_N(R)`, with the orbits of `E_N(R)`. Drop the condition.
- **N2 (the Remark on purely infinite rings).** The Ara–Goodearl–Pardo input, that every class is represented by an
  idempotent, is for the citation lens. Items 1–4 do not use it.
