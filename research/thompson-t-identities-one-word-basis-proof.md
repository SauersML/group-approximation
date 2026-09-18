---
rg: 2
id: thompson-t-identities-one-word-basis-proof
kind: route
title: Move an orientation break into a three-arc configuration with T, squeeze three conjugates into one arc, and read off a nontrivial nested commutator
target: thompson-t-identities-one-word-basis-over-cantor-overgroups
requires:
  - homeo-circle-three-arc-commutator-word-is-mixed-identity
  - circle-overgroups-of-thompson-t-satisfy-all-its-mixed-identities
---

Notation is as in the target. Arcs are dyadic intervals of the cyclic order: cones in `C`, or
arcs with dyadic endpoints in `S^1`. `T_A` is the group of elements of `T` supported in the arc
`A`, a copy of `F` acting on the interior of `A`. For a bijection `f`, `supp f` is the set of
points `f` moves.

**Two facts used throughout.**
- **(D)** If `f` and `g` commute, then `f(supp g) = supp g`. So if `f` moves some point of
  `supp g` outside `supp g`, then `[f, g] ≠ 1`.
- **(S)** Squeezing. Let `A` be an arc, `K` a compact set inside the interior of `A`, and `O` an
  arc strictly inside `A`. Then some `γ ∈ T_A` has `γ(K) ⊆ O`. This is the corresponding fact
  for `F` acting on dyadic intervals of `(0,1)`.

## The word E

- **Arcs.** Take the pairwise disjoint arcs `A_1 = [000]`, `A_2 = [010]`, `A_3 = [100]`, in this
  cyclic order, with nonempty gaps between them.
- **Transport elements.** Fix `c, d ∈ T` with `c(A_2) = A_1` and `d(A_3) = A_1`.
- **Constants.** Fix a nontrivial `a ∈ T_(A_1)`, and put
  `a_1 = a`, `a_2 = c^{−1} a^2 c ∈ T_(A_2)`, `a_3 = d^{−1} a^3 d ∈ T_(A_3)`.
- **The word.** In `T * ⟨x⟩`, with `s_ij = [a_i, x a_j x^{−1}]`, set
  `E = [[s_12, c s_21 c^{−1}], d s_33 d^{−1}]`.

## Step 1. E vanishes on every orientation-preserving map

Let `x` be a bijection of `X` preserving the cyclic order, for instance any element of
`Homeo_cyc(C)` or `Homeo_+(S^1)`.
- By Step 3 of `homeo-circle-three-arc-mixed-identity-proof` (which only uses orientation of
  triples and `supp a_i ⊆ A_i`), one of `s_12(x)`, `s_21(x)`, `s_33(x)` is trivial.
- Either way, the inner or the outer commutator of `E(x)` is trivial.

So `E(x) = 1`, and in particular `E` vanishes on `T`. Step 3 below gives some `h ∈ V` with
`E(h) ≠ 1`. So `E ≠ 1` in `T * ⟨x⟩`, and `E ∈ J_1(T)`.

## Step 2. Moving a break into position

Let `g ∈ M` fail to preserve the cyclic order.
- **The break.** Some positively oriented triple `(p_1, p_2, p_3)` has `(g p_1, g p_2, g p_3)`
  negatively oriented.
- **Arcs around it.** By continuity there are disjoint arcs `B_i ∋ p_i`, positively ordered.
  There are also disjoint arcs `E_i ⊇ g(B_i)`, negatively ordered, so that `(E_2, E_1, E_3)`
  is positively ordered.
- **Two elements of `T`.** `T` maps any cyclically ordered family of disjoint dyadic arcs with
  nonempty gaps into any other of the same size. So there are:
  - `t' ∈ T` with `t'(A_i) ⊆ B_i`;
  - `t ∈ T` sending `E_2`, `E_1`, `E_3` into arcs lying strictly inside `A_1`, `A_2`, `A_3`
    respectively.
- **The result.** `h = t g t' ∈ M` has `h(A_2) ⊆ A_1`, `h(A_1) ⊆ A_2` and `h(A_3) ⊆ A_3`, each
  image compact in the interior of its target.

Put `b_j = h a_j h^{−1}`, so `supp b_j ⊆ h(A_j)`. Then:
- `β_1 = b_2`, `β_2 = c b_1 c^{−1}` and `β_3 = d b_3 d^{−1}` are nontrivial;
- they are supported in compact subsets of the interior of `A_1`;
- by the choice of constants, `s_12(h) = [a, β_1]`, `c s_21(h) c^{−1} = [a^2, β_2]` and
  `d s_33(h) d^{−1} = [a^3, β_3]`.

**Free adjustments.**
- For `u_i ∈ T_(A_i)`, replace `h` by `h' = u_1 u_2 u_3 h ∈ M`.
- The `u_i` have disjoint supports, and `b_2 ⊆ A_1`, `b_1 ⊆ A_2`, `b_3 ⊆ A_3`.
- So this replaces `β_i` by `γ_i β_i γ_i^{−1}`, with `γ_1 = u_1`, `γ_2 = c u_2 c^{−1}` and
  `γ_3 = d u_3 d^{−1}` ranging independently over all of `T_(A_1)`.

## Step 3. Choosing the γ_i makes E(h') nontrivial

**Level 1.**
- Pick `r ∈ supp a`. The points `r, a r, a^2 r, a^3 r` are distinct, since `a` is piecewise
  linear on an interval and has no periodic points in its support.
- Take an arc `O_1 ∋ r` strictly inside `A_1`, so small that `O_1, aO_1, a^2O_1, a^3O_1` are
  pairwise disjoint.
- By (S) choose `γ_1` with `β_1' = γ_1 β_1 γ_1^{−1}` supported in `O_1`.
- Then `X_1 = [a, β_1'] = (a β_1' a^{−1}) · β_1'^{−1}`, with the two factors supported in
  `aO_1` and `O_1`.

**Level 2.**
- Choose `q ∈ supp β_1'` and an arc `O_2 ∋ q` inside `O_1` with `β_1'(O_2) ∩ O_2 = ∅`.
- By (S) choose `γ_2` with `β_2' = γ_2 β_2 γ_2^{−1}` supported in `O_2`.
- Then `X_2 = [a^2, β_2'] = (a^2 β_2' a^{−2}) · β_2'^{−1}`, with factors in `a^2O_2 ⊆ a^2O_1` and in
  `O_2`.
- All factors commute except the two living in `O_1`, so
  `Y = [X_1, X_2] = [β_1'^{−1}, β_2'^{−1}]`, supported in `O_1`.
- `Y ≠ 1` by (D): `β_1'` moves `supp β_2' ⊆ O_2` off itself.

**Level 3.**
- Choose `z ∈ supp Y` and an arc `O_3 ∋ z` inside `O_1` with `Y(O_3) ∩ O_3 = ∅`.
- By (S) choose `γ_3` with `β_3' = γ_3 β_3 γ_3^{−1}` supported in `O_3`.
- Then `X_3 = [a^3, β_3']` has `supp X_3 ⊆ O_3 ∪ a^3O_3`, and `supp X_3 ∩ O_3 = supp β_3'`.
- For `z' ∈ supp β_3'`, the point `Y(z')` lies in `O_1 \ O_3`, so it is outside `supp X_3`,
  because `a^3O_3` misses `O_1`.
- By (D), `E(h') = [Y, X_3] ≠ 1`.

So `M` violates `E`. Taking `g ∈ V` order-breaking and `M = V` gives the `h` needed in Step 1.

## Step 4. Conclusion

- **Item 1.** If `M` satisfies `E`, every `g ∈ M` preserves the cyclic order, by Steps 2 and 3.
- **Item 2, circle case.** `M ≤ Homeo_+(S^1)` contains `T` in its standard action, and part (C)
  of `circle-overgroups-of-thompson-t-satisfy-all-its-mixed-identities` gives
  `J_k(M; T) = J_k(T)`.
- **Item 2, Cantor case.** A cyclic-order-preserving homeomorphism of `C` maps consecutive
  pairs `u01^∞, u10^∞` to consecutive pairs. So it descends to an element of `Homeo_+(S^1)`
  along the binary-expansion map `C → S^1`. This gives an injective homomorphism
  `Homeo_cyc(C) → Homeo_+(S^1)` extending the standard `T`, and part (C) applies to the
  image. ∎
