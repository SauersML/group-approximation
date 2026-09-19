---
rg: 2
id: fpbs-mal-bootstrap-certified-chords-pay-seed-floor-proof
kind: route
title: Charge each chord-cell firing to its chord instance, so the charged b-edges plus the ignition seeds have 2-of-3 closure containing the bootstrap closure
target: fpbs-mal-bootstrap-certified-chords-pay-seed-floor
requires:
  - fpbs-weakly-bernoulli-fold-seeds-have-density-floor
artifacts:
  - experiments/fpbs-chord-bootstrap-2026-09-17/bootstrap_injection.py
  - experiments/fpbs-chord-bootstrap-2026-09-17/bootstrap_injection_out.txt
---

Notation as in the target. Write `P(x)` for the finite set of distinct points
among `s_1(x), …, s_r(x)`. For each `h`, the path word is fixed, so
`P(x) = {g_{h,1} x, …, g_{h,m_h} x}` for fixed `g_{h,i} ∈ L`. Measurable
choices of the path from countably many words work the same way.

**Rounds.** Put `S_0 = A_0` and `S_{n+1} = S_n ∪ T(S_n) ∪ C(S_n)`, where
`T` and `C` apply rules (T) and (C) once to `S_n`. Each `S_n` is a countable
Boolean combination of translates of `A_0` and the `D_h`, so it is
measurable. Each rule has finitely many premises, so
`boot_Φ(A_0) = ∪_n S_n`.

**Firing time.** For `x ∈ D_h`, let `n(x)` be the least `n` with
`|P(x) \ S_n| ≤ 1`, or `∞`. This is measurable in `x`.
- If `|P(x) \ S_{n(x)}| = 1`, call `x` *fired*. Let `j(x)` be the least
  `i` with `g_{h,i} x ∉ S_{n(x)}`, and set `t(x) = g_{h,j(x)} x`.
- Otherwise `x` never adds anything new through (C).

Put `A_1 = { t(x) : x fired }`. Split the fired part of `D_h` into the
pieces `D_{h,i} = {x fired : j(x) = i}`. Then
`A_1 = ∪_{h,i} g_{h,i} D_{h,i}` is measurable, and

```text
μ(A_1) ≤ Σ_h Σ_i μ(D_{h,i}) ≤ Σ_h μ(D_h).
```

**Induction: `S_n ⊆ cl(A_0 ∪ A_1)` for all `n`.** Write `Z` for the right
side. `S_0 = A_0 ⊆ Z`. Suppose `S_n ⊆ Z`.
- `T(S_n) ⊆ Z`, because `Z` is closed under (T).
- Let `z ∈ C(S_n)`, witnessed by `x ∈ D_h`, so `P(x) \ S_n = {z}`. Then
  `n(x) ≤ n`, and `S_{n(x)} ⊆ S_n`.
  - If `|P(x) \ S_{n(x)}| = 0`, then `z ∈ S_n`, which contradicts the
    witness.
  - Otherwise `P(x) \ S_{n(x)} = {t(x)}`. As `z ∉ S_n ⊇ S_{n(x)}`, this gives
    `z = t(x) ∈ A_1 ⊆ Z`.

So `S_{n+1} ⊆ Z`. This proves Item 1, and it uses neither freeness nor
measure preservation beyond the translate bound.

**Item 2.** If `boot_Φ(A_0)` is conull, then `cl(A_0 ∪ A_1)` is conull. By
the definition of `σ_b`,
`σ_b(X) ≤ μ(A_0 ∪ A_1) ≤ μ(A_0) + Σ_h μ(D_h)`. On actions weakly contained
in Bernoulli, `fpbs-weakly-bernoulli-fold-seeds-have-density-floor` gives
`σ_b ≥ 1/80`.

**Item 3.** `red(bbab · (bab)^{-1}) = b`, so on a free action
`R_K ∨ Φ_0 = R_{<K, bab, bbab>} = R_L`. Both labels have b-length 2
(`coset_b_length.py`, re-checked in `bootstrap_injection.py`). So
`|P(x)| ≥ 2` for every instance and every path. From `∅`, rule (C) needs a
known edge and rule (T) needs two, so nothing ever fires.

**Soundness of the rules.** Let `R' = R_K ∨ b|_{A_0} ∨ Φ`.
- For (T): this is Lemma 1.1 of
  `research/artifacts/fpbs-fold-bootstrap-seeding-2026-09-17.md` (the
  inclusion `cl(A) ⊆ D` of `fpbs-mal-fold-closure-exactness`), which holds
  for every action. The b-edges at `w, aw, bw` close up with the `K`-letters
  `a` and `c`, since `c b^2 w = b a w`.
- For (C): the path from `x` to `hx` uses `K`-moves, the b-edges in
  `P(x)`, and the chord `(x, hx) ∈ Φ`. If all but one b-edge lies in `R'`,
  the endpoints of the last one are `R'`-related.

**Check.** `bootstrap_injection.py` runs the bootstrap on 12 random finite
actions (`N = 3000`, seed density `q ≤ 0.1`, chord density `p ≤ 0.1`, word
lengths 3 to 24). In every run:
- the charged seed count is at most `|A_0| + #chords` (worst ratio 0.869);
- the 2-of-3 closure of `A_0 ∪ A_1` equals the bootstrap closure.
