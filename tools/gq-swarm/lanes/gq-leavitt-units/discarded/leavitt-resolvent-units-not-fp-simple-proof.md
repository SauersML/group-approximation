---
rg: 2
id: leavitt-resolvent-units-not-fp-simple-proof
kind: route
title: Apply the central-unit theorem to R_L, whose centre contains Q, with P = [R_L^x, R_L^x] and C = Z(P)
target: leavitt-resolvent-derived-units-mod-centre-not-fp-simple
requires:
  - leavitt-resolvent-ring-is-fp-simple-of-char-zero
  - leavitt-central-units-lie-in-derived-normal-subgroups
---

**Inputs from `leavitt-resolvent-ring-is-fp-simple-of-char-zero`.**
- `R_L ≠ 0`.
- `s_1, s_2, t_1, t_2` form a binary Leavitt family.
- `Q ⊆ R_L` unitally. Every `m · 1` with `m ≥ 1` is central and invertible, so its inverse
  `1/m` is central, and `Q^x ≤ Z(R_L) ∩ R_L^x`.

**Deduction.** Let `U = R_L^x` and `P = D = [U, U]`.
- `P` is normal in `U` and contains `V = [V, V]`.
- By `leavitt-central-units-lie-in-derived-normal-subgroups`, part 1, the central units
  lie in `[D, D]`. They lie in `Z(D)` because they are central in `U`. This proves part 1.
- `Q^x` is not finitely generated, since there are infinitely many primes. Part 2 of the
  theorem with `C = Z(D)` shows that `D/Z(D)` is not a finitely presented perfect group.
- A simple group is perfect unless it is cyclic of prime order. `D/Z(D)` cannot be
  nontrivial cyclic, because then `D` would be abelian and `D/Z(D)` trivial. So `D/Z(D)`
  is not a finitely presented simple group.

QED
