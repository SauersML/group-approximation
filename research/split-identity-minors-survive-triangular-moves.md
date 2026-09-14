---
rg: 2
id: split-identity-minors-survive-triangular-moves
kind: claim
title: Identity minors that split along the diagonal blocks survive triangular moves, and idempotent triangular moves are minor moves
distinct_from:
  sylvester-rank-functions-iff-no-triangular-certificate: that characterizes existence of Sylvester rank functions by identity certificates built from minors and triangular moves; this shows which triangular moves can be removed from such a certificate without leaving the minor order.
artifacts:
  - research/artifacts/state-upgrade-kill-test-2026-09-12.md
---

**ESTABLISHED.** Let `A` be a unital ring. Write `I_n ⊑ Y` if `I_(n+s) <~ Y (+) I_s` for some `s >= 0`,
where `<~` is the minor order `M = X N Y`.

1. **Split minors.** If `I_a ⊑ A` and `I_b ⊑ B`, then `I_(a+b) ⊑ [[A, C], [0, B]]` for every `C`.
2. **Split chains flatten.** Take a chain `I_(q+1) = Y_0, ..., Y_n = I_q` of minor steps and triangular
   steps `A_i (+) B_i (+) Z_i -> [[A_i, C_i], [0, B_i]] (+) Z_i`. If at every triangular step the
   carried `I_(q+1) ⊑ Y_i` splits as `I_a ⊑ A_i`, `I_b ⊑ B_i`, `I_c ⊑ Z_i` with `a + b + c = q + 1`, then
   `I_(q+1+s) <~ I_(q+s)` for some `s`, so `A` fails the rank condition.
3. **Idempotent steps.** If `A`, `B` and `T = [[A, C], [0, B]]` are idempotent matrices, then `C = AC + CB`,
   `ACB = 0`, and conjugation by `[[1, AC - CB], [0, 1]]` carries `T` to `A (+) B`.

**Consequence.** Consider a ring that has the rank condition but no Sylvester matrix rank function, as
in `rank-condition-rings-carry-sylvester-rank-functions`. Its identity certificate must contain a
non-idempotent triangular step at which the carried identity minor mixes the two diagonal blocks. Over
`M_2(K)`, `I_1 ⊑ e_11 (+) e_22` while neither block carries `I_1`, so such mixing is common and part 2
does not by itself prove the regular case.

Proof: Section 3 of the artifact.
