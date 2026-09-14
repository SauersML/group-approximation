---
rg: 2
id: subshift-elementary-groups-are-steinberg-groups-in-finite-rank
kind: claim
title: Open - is EL_n(LC(X,F_2)⋊Z) its own Steinberg group St_n, with trivial Schur multiplier, for some finite n
artifacts:
  - research/artifacts/sk-open-4-dictionary-2026-09-13-part1.md
  - research/artifacts/sk-open-4-dictionary-2026-09-13-part2.md
---

**OPEN.** Let `X` be an infinite minimal subshift and `R_X = LC(X,F_2) ⋊_T Z`. Is there a finite `n ≥ 3`, ideally
`n = 3`, with `St_n(R_X) → EL_n(R_X)` an isomorphism and `H_2(EL_n(R_X);Z) = 0`?

A positive answer would give an explicit presentation of the note's simple Kazhdan LEF groups by Steinberg relations over
`R_X`, and would identify their Schur multipliers.

## Attempts

- **Stable case.** For every Cantor homeomorphism, `K_2(R_X) = 0` over `F_2`. The algebraic Pimsner–Voiculescu sequence
  has `K_2(LC(X,F_2)) = K_1(LC(X,F_2)) = 0` (artifact part 1, §3). So `St(R_X) = E(R_X)`, and `E(R_X)` is centrally
  closed.
  - **Where it dies:** passing to finite `n` needs injective stability `K_2(n,R) → K_2(R)` (van der Kallen), which holds only in a range `n ≥ sr(R) + c`. No finite stable-rank bound for `R_X` is established on main. Lanes sk-stable-rank-a/b own `sr(R_X)`.
- **Central closure in finite rank.** `St_n(R)` is centrally closed for `n ≥ 5` (Kervaire, for any ring). So a stable-range bound `sr(R_X) ≤ n − c` with `n ≥ 5` would settle the question at that `n`. Ranks 3 and 4 need separate arguments.
- **Firewall for ranks 3 and 4 over F_2-algebras.** `SL_3(F_2)` and `SL_4(F_2) ≅ A_8` have Schur multiplier `Z/2`. So small-rank Steinberg groups over `F_2`-algebras can carry extra central extensions, and nothing is claimed at `n = 3, 4` without a proof. This firewall is not itself a proof that `n = 3` fails.
- **Homology.** In a homology stability range (van der Kallen), `H_3(EL_n(R_X)) ≅ H_3(E(R_X)) ≅ K_3(R_X) ≅ K^0(X,T)/3`. That would make the dimension group mod 3 a group-homological isomorphism invariant of `EL_n(R_X)` for large `n`. It has the same stable-rank dependence.
