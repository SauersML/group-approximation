---
rg: 2
id: kourovka-7-19-via-small-cancellation-bh
kind: route
title: A constructive Boone-Higman embedding of one explicit C'(1/6) group G_A with non-primitive-recursive A answers Kourovka 7.19
target: kourovka-7-19-explicit-fp-simple-group-with-non-pr-word-problem
requires: [graphical-small-cancellation-inputs-satisfy-boone-higman, small-cancellation-groups-realize-every-wp-complexity]
---

1. **The set `A`.** Fix a standard enumeration `(f_n)` of primitive recursive definitions of unary functions,
   and put `A = {n : f_n(n) = 0}`. Then `A` is decidable, since each `f_n` is total and computable uniformly in
   `n`. And `A` is not primitive recursive, by diagonalization: if `χ_A = f_m`, then `m ∈ A` iff `f_m(m) = 0`
   iff `χ_A(m) = 0` iff `m ∉ A`, with `χ_A(m) = 1` exactly for `m ∈ A`.
2. **The group `G_A`.** In `small-cancellation-groups-realize-every-wp-complexity`, `G_A = <a,b | r_n (n in A)>`
   is two-generator classical `C'(1/6)` with solvable word problem, and `r_n = 1` in `G_A` iff `n ∈ A` (item 2).
3. **Hardness.** The map `n ↦ r_n` is primitive recursive, with length `O(4^n)`. So if the word problem of
   `G_A` were primitive recursive, so would `A` be. It is not.
4. **The embedding.** `graphical-small-cancellation-inputs-satisfy-boone-higman` (OPEN) gives `G_A ≤ S` with `S`
   finitely presented and simple. The inclusion is a linear-time substitution on words, so the word problem of
   `S` is not primitive recursive either. `∎`

**Explicitness.** The printed question asks for an explicit `S`. This route delivers one only if the proof of
step 4, for this particular `A`, constructs `S` from the relators of `G_A`. An existence proof, for example one
by Zorn's lemma, would answer only the existence form.
