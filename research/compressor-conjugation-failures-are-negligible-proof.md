---
rg: 2
id: compressor-conjugation-failures-are-negligible-proof
kind: route
title: Split the ambient conjugation defect at A(t g t^-1), count failures as disagreements of conjugates, and add the blocks up
target: compressor-conjugation-failures-are-negligible
requires: []
artifacts:
  - GroupApproximation/KunThom/ConjugationFailureVanishing.lean
---

Proved in Lean in `GroupApproximation/KunThom/ConjugationFailureVanishing.lean`.

- **Probe.** GREEN record `kt41-seq-wrapper.green.0912-135611-30832` (base d4e2f2429,
  md5 bf11670084b5e8ad0828a9356b1d90be).
- **Axioms.** All six printed closures lie within `[propext, Classical.choice, Quot.sound]`.

1. **Words.** By induction on the word, `wordAct (fun l => tau (iota l)) w` equals
   `evaluateWord tau (w.map iota)`: both are left-to-right products.
2. **Ambient defect.** The triangle inequality at `A_n(t g t^-1)`:
   - `d_H(u A(g) u^-1, A(t g t^-1))` vanishes by `hamming_conj_vanishing`;
   - `A(t g t^-1) = A((w.map iota).prod)` by the word hypothesis;
   - `d_H(A(prod), evaluateWord)` vanishes by `word_close` through
     `vanishing_of_eventually_lt`.
3. **Counts.** `y -> q y` maps `{y | q(a y) != b(q y)}` injectively into the
   disagreement of `q a q^-1` and `b`. For the inverse form, apply this with
   `q^-1`. Left invariance by `q` and right invariance by `q^-1` give
   `d_H(q^-1 b q, a) = d_H(q a q^-1, b)`.
4. **Totals.** `sum_card_conjFailure_le` bounds each label's block total by its
   ambient count. On a failure point, rewrite the ambient label action to
   `A_n(iota s)` and the word action to `wordAct` of the mapped labels. Sum the
   per-label negligible counts over the finite label set with `Negligible.sum`,
   and finish with `Negligible.mono_nonneg`.
