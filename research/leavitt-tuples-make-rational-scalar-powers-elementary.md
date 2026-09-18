---
rg: 2
id: leavitt-tuples-make-rational-scalar-powers-elementary
kind: claim
title: In a ring containing Q and a Leavitt (1,d)-tuple, every (d-1)-th power of a rational scalar is elementary, so the scalar budget fails
artifacts:
  - research/artifacts/gq-referee-a-bounded-harmonic-rings-are-not-finitely-presented.md
distinct_from:
  leavitt-centralizer-units-are-elementary-in-rank-three: that is the case d = 2 (a Leavitt pair), where every scalar is elementary; this is every d >= 2, where the (d-1)-th powers are.
  rational-scalars-obstruct-fp-elementary-hosts: that shows the elementary rational scalars of a projective-elementary host must form a finitely generated group; this shows that group contains (Q^x)^(d-1), which is not finitely generated, whenever the ring has a Leavitt (1,d)-tuple.
---

**ESTABLISHED (2026-09-18)** through `leavitt-tuples-make-rational-scalar-powers-elementary-proof`.
Lane proof (`gq-steinberg-q`), elementary. `gq-referee-a` PASS, proof-gap lens
(`research/artifacts/gq-referee-a-bounded-harmonic-rings-are-not-finitely-presented.md`, which covers both nodes); `gq-referee-b` pending.

**Statement.** Let `d >= 2`. Let `S` be a unital ring with `Q ⊆ S` and elements `x_1, …, x_d, y_1, …, y_d`
satisfying `y_i x_j = δ_ij` and `Σ_i x_i y_i = 1`. Then:
- `diag(u^(d-1), 1, …, 1) ∈ E_m(S)` for every `m >= d+1` and every unit `u` commuting with all `x_i`, `y_i`;
- in particular `q^(d-1) I_m ∈ E_m(S)` for every `q ∈ Q^x`, and these scalars are central;
- so `Λ_m(S) ⊇ (Q^x)^(d-1)`, which is not finitely generated.

Hence no such `S` satisfies condition 3 of `q-algebra-with-fp-simple-projective-elementary-group`, and no
`Q`-algebra with a Leavitt `(1,d)`-tuple is a projective-elementary host. This covers:
- Leavitt algebras `L_Q(1,d)`;
- `R_L`;
- purely infinite Leavitt path and Nekrashevych-type rings with such a tuple;
- tensor products `B ⊗ L_Z(1,d)`.

## Proof

1. **The swap matrix is elementary.** Let `𝒴 = (y_1, …, y_d)^T` and `𝒳 = (x_1, …, x_d)`, so `𝒳𝒴 = 1` and
   `𝒴𝒳 = I_d`. Put `W = [[𝒴, 0], [0, 𝒳]] ∈ M_(d+1)(S)`, with inverse `[[𝒳, 0], [0, 𝒴]]`. Apply these
   elementary operations:
   - `row_(d+1) += Σ_i x_i · row_i`, giving the row `(1, x_1, …, x_d)`;
   - `row_i -= y_i · row_(d+1)` for each `i`, giving `(0, -e_i)`;
   - `col_(j+1) -= col_1 · x_j` for each `j`.

   This turns `W` into `P = [[0, -I_d], [1, 0]]`. Its permutation is a `(d+1)`-cycle and it has `d` minus
   signs, so `det P = (-1)^d (-1)^d = 1`, and `P ∈ SL_(d+1)(Z) = E_(d+1)(Z)`. Hence `W ∈ E_(d+1)(S)`.
2. **Doubling the unit.** For `u` commuting with the tuple, `W diag(u, I_d) W^(-1) = diag(𝒴 u 𝒳, 𝒳𝒴)
   = diag(u I_d, 1)`. With `D = diag(u, I_d)`, `D W^(-1) D^(-1) ∈ E_(d+1)(S)`, because diagonal conjugation
   preserves elementary matrices. So
   `diag(1, u, …, u, 1) = W D W^(-1) D^(-1) ∈ E_(d+1)(S)`, with `d-1` copies of `u`.
3. **Collecting.** `diag(b, b^(-1)) ∈ E_2(S)` by Whitehead's `2×2` formula, and signed permutations of
   determinant 1 lie in `E_(d+1)(Z)`. So `diag(1, u, …, u, 1) ≡ diag(u^(d-1), 1, …, 1)` modulo `E_(d+1)(S)`.
   Stabilize to any `m >= d+1`.
4. **Scalars.** `q ∈ Q^x` is central in `S` (the inverse of a central unit is central), so it commutes with
   the tuple. `q^(d-1) I_m` is a product of `m` conjugates of `diag(q^(d-1), 1, …)` by signed permutation
   matrices of determinant 1. These lie in `E_m(Z)`, so the conjugates stay in `E_m(S)`. Plain permutation
   matrices need not normalize `E_m` over a noncommutative ring. Because `q^(d-1)` is central, the signs do not
   change the conjugate.
   `(Q^x)^(d-1)` contains `p^(d-1)` for every prime `p`, so it is free abelian of infinite rank modulo
   torsion, and not finitely generated.
