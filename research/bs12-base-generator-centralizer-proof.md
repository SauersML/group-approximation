---
rg: 2
id: bs12-base-generator-centralizer-proof
kind: route
title: Put BS(1,4) = <a^2, b> in PSL_2(Z[1/2]), cut out <b> by the tree-vertex stabilizer PSL_2(Z), and induce from index two
target: bs12-base-generator-is-a-centralizer-in-b-a
requires:
  - lamp-wreaths-over-psl2-tree-vertices-lie-in-b-a
  - pbh-coset-wreaths-iff-identity-edge-hnns
  - boone-higman-type-a-class-closed-under-finite-extensions
---

Lane proof (bh-free-49, 2026-09-18), not reviewed. `A = <a, b | a^-1 b a = b^2>` is
`Z[1/2] ⋊ <a>`, with `b = 1` in the base `Z[1/2]` and `a^-1 q a = 2q` there.

**Step 0 (faithfulness of Baumslag--Solitar images).** Let `n >= 2` and `N ⊴ BS(1,n)`
nontrivial. If `N` met the base `Z[1/n]` trivially, then `[N, Z[1/n]] = 1`, but the
centralizer of the base is the base. So `N` contains a nonzero `q ∈ Z[1/n]`, and then a
nonzero integer multiple of the base generator (multiply `q` by a power of `n`). So a
quotient of `BS(1,n)` in which the base generator has infinite order is faithful.

**Step 1 (BS(1,4) in PSL_2(Z[1/2])).** Let `Δ = <a^2, b> = Z[1/2] ⋊ <a^2> ≅ BS(1,4)`, of
index two in `A`. Put `G = PSL_2(Z[1/2])`, `H = PSL_2(Z)`, `u = ±[[1,1],[0,1]]` and
`w = ±diag(1/2, 2)`. Then `w^-1 u w = u^4`, so `ε(b) = u`, `ε(a^2) = w` defines a
homomorphism `ε : Δ -> G`, injective by Step 0 because `u` has infinite order. An element
`b^q a^(2k)` maps to `±[[2^-k, 2^k q], [0, 2^k]]`, which lies in `H` iff `k = 0` and
`q ∈ Z`. So `ε^-1(H) = <b>`.

**Step 2 (the vertex lamp).** By `lamp-wreaths-over-psl2-tree-vertices-lie-in-b-a`
(`m = 1`, lamp group `Z/2`), `L_0 = Z/2 wr_(G/H) G ∈ B_A`. Its lamp `m_0 = δ_H` satisfies
`g m_0 g^-1 = δ_(gH)`, so `C_G(m_0) = H`, and `C_Δ(m_0) = <b>` through `ε`.

**Step 3 (index two).** Let `L_1 = L_0 wr Z/2 = (L_0 × L_0) ⋊ <σ>`. It lies in `B_A`,
because it contains `L_0 × L_0` with index two
(`boone-higman-type-a-class-closed-under-finite-extensions`). With transversal `{1, a}`
of `Δ` in `A`, the Kaloujnine--Krasner map `κ` sends
- `γ ∈ Δ` to `((ε(γ), ε(a^-1 γ a)), 1)`;
- `γ = a δ` (`δ ∈ Δ`) to `((ε(δ), ε(a δ a)), σ)`.

It is an injective homomorphism `A -> L_1`. Let `m = ((m_0, m_0), 1)`. Conjugating `m`
by `((f_1, f_2), σ^e)` gives `(f_1 m_0 f_1^-1, f_2 m_0 f_2^-1)`, possibly swapped. So
`κ(γ)` commutes with `m` iff both coordinates of `κ(γ)` lie in `C_(L_0)(m_0)`.
- For `γ ∈ Δ`, this means `γ ∈ <b>` and `a^-1 γ a ∈ <b>`. The second follows from the
  first, since `a^-1 b^n a = b^(2n)`. So `C_Δ(m) = <b>`.
- For `γ = a δ`, it needs `δ ∈ <b>` and `a δ a ∈ <b>`. But `δ ∈ <b>` has `a`-exponent `0`,
  so `a δ a` has `a`-exponent `2` and is not in `<b>`.

So `C_A(m) = <b>`, which is item 1. []

**Step 4 (consequences).** Item 1 is condition (e) of
`pbh-coset-wreaths-iff-identity-edge-hnns` for `(A, C)`. So (b), (c) and (d) hold, which
are the three groups of item 2. `E` is finitely generated and lies in `B_A`, so it embeds
in a finitely presented simple group (`type-a-action-gives-boone-higman-for-subgroups`). []

**Step 5 (not quasi-linear).** Let `b_1 = a b a^-1`, so `b_1^2 = b` and `b_1 ∉ <b>`.
- In `E = A *_C (C × <t>)`, the word `t b_1 t^-1 b_1^-1` has no pinch, because
  `b_1 ∉ C`. By Britton's lemma it is not `1`.
- Let `ρ` be a homomorphism from `E` to `GL_n(F)`. Since `b` is conjugate to `b^2`, the
  eigenvalues of `ρ(b)` are closed under squaring, so they are roots of unity. In
  characteristic `p` this makes `ρ(b)` of finite order. Then `ρ(b_1)`, which is
  conjugate to `ρ(b)`, has the same odd order `n'`, and `ρ(b_1)^2 = ρ(b)` gives
  `ρ(b_1) = ρ(b)^((n'+1)/2)`, which commutes with `ρ(t)`. In characteristic `0`,
  `ρ(b) = s v` with `s` of finite order and `v` unipotent. The Zariski closure of
  `<ρ(b)>` is `<s> × {v^x : x ∈ F}`, and it contains `ρ(b_1)`: `ρ(b_1)` has unipotent part
  `v^(1/2)`, and its semisimple part has odd order and squares to `s`, so it lies in
  `<s>`. The centralizer of `ρ(t)` is Zariski closed and contains `ρ(b)`, so it contains
  `ρ(b_1)`.
- In both cases `[ρ(t), ρ(b_1)] = 1`. The same then holds in any finite product of
  linear groups. []
