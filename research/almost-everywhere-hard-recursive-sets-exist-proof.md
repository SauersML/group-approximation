---
rg: 2
id: almost-everywhere-hard-recursive-sets-exist-proof
kind: route
title: Cancel each machine the first time it is fast and uncancelled, and answer against it
target: almost-everywhere-hard-recursive-sets-exist
requires: []
---

Fix a standard enumeration `M_0, M_1, ...` of deterministic Turing machines, with
step-counted universal simulation. Fix total recursive `F`.

**Construction.** Define by recursion on `i = 0, 1, 2, ...` a bit `A(i)` and a
finite set `C_{i+1} ⊇ C_i` of cancelled indices, with `C_0 = ∅`.

- The *candidates at stage `i`* are the indices `e <= i` with `e ∉ C_i` such that
  `M_e` on input `i` halts within `F(i)` steps with output `0` or `1`.
- If there is a candidate, let `e` be the least one, put `A(i) = 1 - M_e(i)` and
  `C_{i+1} = C_i ∪ {e}`.
- Otherwise put `A(i) = 0` and `C_{i+1} = C_i`.

**`A` is recursive.** To compute `A(i)`, run stages `0, ..., i`. Stage `j`
computes `F(j)` and simulates at most `j + 1` machines for `F(j)` steps each,
so every stage terminates.

**Hardness.** Let `M_e` decide `A`, and suppose, for contradiction, that the set
`I` of inputs `i` on which `M_e` halts within `F(i)` steps is infinite.

1. `e` is never cancelled. If `e` were cancelled at stage `j`, then
   `A(j) = 1 - M_e(j) ≠ M_e(j)`, so `M_e` does not decide `A`.
2. Only the finitely many indices `e' < e` could precede `e`. Each is cancelled
   at most once, so there is a stage `j_0` such that every `e' < e` that is ever
   cancelled is already in `C_{j_0}`.
3. Take `i ∈ I` with `i >= max(e, j_0)`. At stage `i`, `e <= i`, `e ∉ C_i`
   by 1, and `M_e(i)` halts within `F(i)` steps with output `A(i) ∈ {0,1}`.
   So `e` is a candidate, and the least candidate `e*` satisfies `e* <= e` and
   is cancelled at stage `i`.
4. By 1, `e* ≠ e`, so `e* < e` and `e*` is cancelled at stage `i >= j_0`. By
   2, `e*` was already in `C_{j_0} ⊆ C_i`, so it was not a candidate at stage
   `i`. Contradiction.

So `I` is finite: every machine deciding `A` runs more than `F(i)` steps on all
but finitely many `i`. `∎`
