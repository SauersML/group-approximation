---
rg: 2
id: mixed-level-root-group-is-not-kazhdan-in-rank-four-proof
kind: route
title: Kill x_i, read off the {1,4}-corner homomorphism onto E_2(F_q[y]), and let it act on Nagao's tree
target: mixed-level-root-group-is-not-kazhdan-in-rank-four
requires:
  - polynomial-gl2-over-a-field-is-a-nontrivial-amalgam
  - property-t-implies-property-fa
---

**1. Specialize.** Pick `j ≠ i`, which exists because `d >= 2`. Define `φ : R_+ -> F_q[y]` by `x_i -> 0`, `x_j -> y`, and
all other variables `-> 0`. Let `Φ = EL_4(φ)`. Every generator with `eps_cd >= 1` has entries in `(x_i)`, so `Φ` kills
it. Hence

```text
Φ(K_i) = < e_cd(F_q[y]) : c ≠ d, c ≠ 3, d ≠ 2 >.
```

**2. A corner homomorphism.** Let `P = { g ∈ SL_4(F_q[y]) : g e_2 = e_2, e_3^T g = e_3^T }`.

- `P` is a subgroup, and it contains every generator above, because `E_cd` has zero column 2 when `d ≠ 2` and zero
  row 3 when `c ≠ 3`.
- For `g, h ∈ P` and `a, b ∈ {1, 4}`, we have `g_a2 = 0` and `h_3b = 0`. So `(gh)_ab = g_a1 h_1b + g_a4 h_4b`.
- So `ρ(g) = (g_ab)_(a, b ∈ {1,4})` is a homomorphism `P -> GL_2(F_q[y])`.
- `ρ` sends `e_14(s)` to `e_12(s)` and `e_41(s)` to `e_21(s)`, and every other generator to `1`. So
  `ρ Φ(K_i) = E_2(F_q[y])`, which proves item 1.

**3. No property (T).** Let `k = F_q` and `E = E_2(k[y]) <= GL_2(k[y])`. By
`polynomial-gl2-over-a-field-is-a-nontrivial-amalgam`, `GL_2(k[y])` acts without inversions on a tree. Its vertex
stabilizers are conjugates of `GL_2(k)` or of `B(k[y])`.

- `E` is infinite, so it lies in no conjugate of the finite group `GL_2(k)`.
- A conjugate `g B(k[y]) g^(-1)` preserves the line `g(k(y) e_1)` in `k(y)^2`. But `e_12(1)` preserves only the line
  `k(y) e_1`, and `e_21(1)` preserves only `k(y) e_2`. Each is unipotent with a one-dimensional eigenspace. So `E`
  preserves no line and lies in no conjugate of `B(k[y])`.
- So `E` fixes no vertex. Since the action has no inversions, `E` fixes no point of the tree, and `E` fails property FA.
- By `property-t-implies-property-fa`, `E` does not have property (T).
- Property (T) passes to quotients (Bekka–de la Harpe–Valette, Thm 1.3.4). So `K_i`, which maps onto `E`, does not
  have property (T). This proves item 2.

**4. Infinite abelianization for `q = 2`.** `F_2[y]` is Euclidean with unit group `{1}`, so
`E_2(F_2[y]) = SL_2(F_2[y]) = GL_2(F_2[y])`. Abelianization preserves pushouts, so

```text
GL_2(F_2[y])^ab = ( GL_2(F_2)^ab ⊕ B(F_2[y])^ab ) / image of B(F_2)^ab.
```

Here `B(F_2[y]) = { [[1, f], [0, 1]] } ≅ (F_2[y], +)` is infinite abelian, and `B(F_2)^ab` has order 2. So the quotient
is infinite, and so is `K_i^ab`, which maps onto it. This proves item 3. ∎
