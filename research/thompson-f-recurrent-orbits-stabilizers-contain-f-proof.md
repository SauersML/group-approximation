---
rg: 2
id: thompson-f-recurrent-orbits-stabilizers-contain-f-proof
kind: route
title: Three rank-three tests inside F plant a stabilizer element with an orbital ending at v, then a straddling bump makes a one-sided approach and Brin gives F
target: thompson-f-recurrent-orbits-have-stabilizers-containing-f
requires:
  - recurrent-orbits-force-every-z3-to-meet-the-stabilizer
  - brin-plo-i-one-sided-approach-gives-a-copy-of-f
---

Realize `F_0 = F ≤ PL_o(I)` in the standard way. Use the one-bump elements `b_{c,d}`
(for dyadic `c` and `d = c + 2^{-k}`) from
`nontrivial-normal-subgroups-of-f-contain-f-proof`: `b_{c,d} ∈ F`, and `b_{c,d}^e`
has the single orbital `(c,d)` for `e ≠ 0`. If three such bumps have pairwise disjoint
supports, they generate a copy of `Z^3`. On `(c_i, d_i)`, the product
`b_1^{e_1} b_2^{e_2} b_3^{e_3}` agrees with `b_i^{e_i}`, so it is trivial only when
every `e_i = 0`.

Let `H = G_x ∩ F_0`. The rank-three test
(`recurrent-orbits-force-every-z3-to-meet-the-stabilizer`, part 2) says that
`A ∩ G_x ≠ 1` for every `A ≤ G` with `A ≅ Z^3`. Every such `A ≤ F_0` has
`A ∩ G_x ⊆ H`.

**Step 1 (planting three stabilizer elements).** Let `I_1 = (1/8, 2/8)`,
`I_2 = (3/8, 4/8)` and `I_3 = (5/8, 6/8)`. Each `I_i = (p_i, p_i + 1/8)` contains three
disjoint bumps `b_{p_i + j/32, p_i + (j+1)/32}`, `j = 0, 1, 2`. These generate
`A_i ≅ Z^3`, all of whose elements are supported in `I_i`.

- The rank-three test gives `1 ≠ f_i ∈ A_i ∩ G_x ⊆ H` with `supp f_i ⊆ I_i`.
- `f_i` is piecewise linear, so `supp f_i` is a finite union of open intervals.
- Let `(u_i, v_i)` be the rightmost one. So `v_i = sup supp f_i ≤ p_i + 1/8`, and
  `(u_i, v_i)` is an orbital of `f_i`.

**Step 2 (straddling bumps).** Choose `k_i ≥ 5` with `δ_i := 2^{-k_i} < v_i − u_i`,
and a dyadic rational `c_i` with `v_i − δ_i < c_i < v_i` (dyadic rationals are dense).
Put `d_i = c_i + δ_i`.

- Then `u_i < c_i < v_i < d_i ≤ p_i + 1/8 + 1/32`.
- So `(c_i, d_i) ∪ I_i ⊆ R_i := (p_i, p_i + 5/32)`. The intervals
  `R_1 = (4/32, 9/32)`, `R_2 = (12/32, 17/32)` and `R_3 = (20/32, 25/32)` have pairwise
  disjoint closures.
- Let `a_i = b_{c_i, d_i}`. The `a_i` have disjoint supports, so
  `A = ⟨a_1, a_2, a_3⟩ ≅ Z^3`.
- The rank-three test gives `1 ≠ w = a_1^{e_1} a_2^{e_2} a_3^{e_3} ∈ H`. Fix `j` with
  `e_j ≠ 0`.
- Then `supp w = ∪_{e_i ≠ 0} (c_i, d_i)`, and the only orbital of `w` inside `R_j` is
  `(c_j, d_j)`.

**Step 3 (one-sided approach).** Let `H′ = ⟨f_j, w⟩ ≤ H`. Its support is
`supp f_j ∪ supp w`. Inside `R_j` this is `supp f_j ∪ (c_j, d_j)`, and the rest lies
in the other `R_i`, whose closures miss `R_j`. Let `B = (a, b)` be the orbital of `H′`
containing `(c_j, d_j)`.

- **Right end.** Every `t ∈ [d_j, p_j + 5/32)` satisfies `t > v_j = sup supp f_j`,
  and `t ∉ (c_j, d_j)`. So `t` is fixed by `H′`, and `b = d_j`.
- **Left end.** `(u_j, v_j) ∪ (c_j, d_j) = (u_j, d_j)` is connected, so `a ≤ u_j < c_j`.
- **Brin's criterion.** The only orbital of `w` lying in `B` is `(c_j, d_j)`. It has
  `b` as an endpoint, and its other endpoint `c_j` differs from `a`. So `w` approaches
  `b` in `B` but not `a`.
- By Brin's Theorem 1, `H′` contains a subgroup isomorphic to `F`. Hence so does
  `H = G_x ∩ F_0`. ∎

**Corollary 1.** Take `G = F` and `F_0 = F`; the stabilizer of a point in a recurrent
orbit contains a copy of `F`.

**Corollary 2.** If `G_x` is amenable, so is its subgroup `H′ ⊇ F`, hence `F` is
amenable. The recurrence method therefore returns the amenability of `F` as an input.
