---
rg: 2
id: leavitt-resolvent-ring-is-fp-and-contains-q
kind: claim
title: The six-generator Leavitt resolvent ring R_L is finitely presented, nonzero, contains Q unitally, and carries a Leavitt pair
distinct_from:
  leavitt-resolvent-ring-is-fp-simple-of-char-zero: that also asserts simplicity of R_L and R_L ≅ M_n(R_L); this is only part 1 (finite presentation, a unital copy of Q, and the Leavitt pair), which needs neither simplicity nor the matrix isomorphism.
---

**ESTABLISHED (2026-09-17)** through `leavitt-resolvent-ring-is-fp-and-contains-q-proof`.
This is part 1 of `leavitt-resolvent-ring-is-fp-simple-of-char-zero` (ring from lanes
`gq-ring-fp-simple` and `gq-malcev-ring`), split off so that uses of it do not wait on
the simplicity proof. `gq-referee-b` checked this direct proof in
`research/artifacts/gq-referee-b-leavitt-pairs-embed-sl-n-q-in-steinberg-groups.md`.

**Statement.** Let

    R_L = Z< s_1, s_2, t_1, t_2, N, A |
             t_i s_j = δ_ij,  s_1 t_1 + s_2 t_2 = 1,
             N s_1 = s_1 (N + 1),  N s_2 = 0,  A (N+1) = 1 = (N+1) A >.

Then:
- `R_L` is finitely presented, with 6 generators and 9 relations;
- `R_L ≠ 0`;
- every integer `m >= 1` is a unit of `R_L`, so `Q ⊆ Z(R_L)` as a unital subring;
- `(s_1, s_2, t_1, t_2)` is a Leavitt pair: `t_i s_j = δ_ij` and `s_1 t_1 + s_2 t_2 = 1`.

## Proof

- **Finitely presented, and a Leavitt pair.** Both hold by definition.
- **Units.** By induction `N s_1^k = s_1^k (N + k)`, so with `X = s_1^(m-1) s_2`:

      (N+1) X = s_1^(m-1) (N + m) s_2 = m X,

  using `N s_2 = 0`. Multiply by `A` on the left: `X = m A X`. Put
  `u_m = t_2 t_1^(m-1) A X`. Then `m u_m = t_2 t_1^(m-1) X = t_2 s_2 = 1`, by
  `t_1 s_1 = 1` and `t_2 s_2 = 1`. Since `m` is central, `u_m = 1/m`. The inverse of a
  central unit is central, so `Q ⊆ Z(R_L)`.
- **Nonzero.** Let `X` be the set of infinite words over `{1,2}` that end in `2^∞`, and let
  `R_L` act on `Q^(X)`:
  - `s_i e_ξ = e_(iξ)`;
  - `t_i e_(iξ) = e_ξ` and `t_i e_(jξ) = 0` for `j ≠ i`;
  - `N e_ξ = λ(ξ) e_ξ`, where `λ(ξ)` is the number of leading 1's of `ξ`, finite on `X`;
  - `A e_ξ = (λ(ξ)+1)^(-1) e_ξ`.

  The nine relations hold:
  - `N s_1 e_ξ = (λ(ξ)+1) e_(1ξ) = s_1 (N+1) e_ξ`;
  - `N s_2 e_ξ = λ(2ξ) e_(2ξ) = 0`;
  - `s_1 t_1 + s_2 t_2` fixes `e_ξ`, because every `ξ` starts with exactly one letter;
  - `t_i s_j = δ_ij` and `A(N+1) = (N+1)A = 1` are immediate.

  So `R_L` has a nonzero module, and `R_L ≠ 0`.
