---
rg: 2
id: pbh-coset-wreaths-iff-identity-edge-hnns-proof
kind: route
title: Lamp at the base coset, partial conjugation of x in Aut_M(M * F_2) with point stabilizers C_G(m), and the stable letter of the identity-edge HNN
target: pbh-coset-wreaths-iff-identity-edge-hnns
requires:
  - free-permutational-products-preserve-pbh
  - type-a-actors-closed-under-type-a-lamp-wreaths
  - relative-automorphism-of-fp-simple-mif-group-has-type-a-action
  - fp-simple-highly-transitive-groups-satisfy-pbh
  - boone-higman-type-a-class-closed-under-finite-extensions
  - permutational-boone-higman-closed-under-wreath-products
  - type-a-action-gives-boone-higman-for-subgroups
---

Lane proof (bh-free-10, 2026-09-18), not reviewed. `G ∈ B_A`, `C <= G`.

**(a) ⟹ (e).** Take `L = Z/2 wr_(G/C) G` and `m = δ_C`, the lamp at the coset `C`.
Then `g δ_C g^(-1) = δ_(gC)`, which equals `δ_C` iff `gC = C` iff `g ∈ C`. So
`C_G(m) = C`.

**(e) ⟹ (b).**
- **The actor.** `L ∈ B_A`, so `L` lies in a type (A) actor `E`. `E` is finitely
  generated, and BFFHZ Theorem C, (i) ⟹ (iv) (`fp-simple-highly-transitive-groups-satisfy-pbh`),
  embeds it in a finitely presented simple MIF group `M`. So `G <= L <= M` and `m ∈ M`.
  By BFFHZ Theorem E (`relative-automorphism-of-fp-simple-mif-group-has-type-a-action`),
  `Ω = Aut_M(M * F(x, y))` acts with type (A) on `S = Hom_M(M * F(x, y), M)`, by
  `α·φ = φ ∘ α^(-1)`. Identify `φ` with `(φ(x), φ(y)) ∈ M × M`.
- **Partial conjugations.** For `h ∈ M`, `π_h` fixes `M` and `y` and sends
  `x -> h x h^(-1)`. Then `π_h π_(h') = π_(h h')`, and `π_h = id` forces `h = 1`. So
  `π: M -> Ω` is an injective homomorphism.
- **Point stabilizers.** `π_g · (m_1, m_2) = (g^(-1) m_1 g, m_2)`, because
  `π_g^(-1)(x) = g^(-1) x g`. So the stabilizer of `s_0 = (m, 1)` in `π(G)` is
  `π(C_G(m)) = π(C)`, and `G·s_0 ≅ G/C` as `G`-sets.
- **The lamps.** If `A = 1` there is nothing to prove. Otherwise `A <= Λ` for a type (A)
  actor `Λ != 1` on a set `Y`. Extend lamp functions on the `π(G)`-invariant subset
  `G·s_0` by `1` elsewhere. This gives an injective homomorphism
  `A wr_(G·s_0) G -> Λ wr_S Ω`, `(f, g) -> (f extended, π_g)`. It is equivariant because
  `G·s_0` is `π(G)`-invariant.
- **Conclusion.** `Λ wr_S Ω` acts on `S × Y` with type (A)
  (`type-a-actors-closed-under-type-a-lamp-wreaths`). So `A wr_(G/C) G ∈ B_A`.

**(b) ⟹ (a).** Take `A = Z/2`, which lies in `B_A` since `Z/2 <= V`.

**(a) ⟹ (c).** This is Part 1 of `free-permutational-products-preserve-pbh-proof`, with
`X = G/C`. The identification `G *_C (C × K) ≅ (*_(G/C) K) ⋊ G` in its Part 3 uses only
that `C` commutes with `K`, not that `C` is finite.

**(c) ⟹ (d).** Take `K = Z`.

**(d) ⟹ (e).** Take `L = G *_C (C × <t>)` and `m = t`.
- `C <= C_G(t)`.
- If `g ∈ G \ C`, the word `t^(-1) g t g^(-1)` has one `t` and one `t^(-1)`, and no
  pinch, because `g ∉ C`. By Britton's lemma it is not `1`, so `g` does not commute
  with `t`.

**Multiple orbits.**
- **One overgroup.** Suppose `C_i = C_G(m_i)` with every `m_i ∈ L`. Choose distinct
  `n_i ∈ M`; this is possible because `M` is infinite. Then the points `(m_i, n_i)` lie
  in distinct `π(G)`-orbits, since `π(G)` does not change the second coordinate. Their
  orbits are `G/C_i`. The lamp embedding above works on the union of these orbits.
- **Free permutational product.** Use Part 1 of
  `free-permutational-products-preserve-pbh-proof`, with the lamp wreath just obtained.
- **Finitely many separate overgroups.** For `L_1, ..., L_n`, embed `G` diagonally in
  `L_1 × ... × L_n ∈ B_A`. Put `m_i` in the `i`-th factor. Then `C_G(m_i)` is unchanged.

**When (e) holds.**
1. **`C` finite.** Main's wreath theorem gives `L = Z/2 wr_(G/C) G ∈ B_A`
   (`permutational-boone-higman-closed-under-wreath-products`). Then apply (a) ⟹ (e).
2. **`C_G(S)` for a finite `S ⊂ G`.** Each `C_G(s)` is realized with `L = G` and `m = s`.
   Then use 5.
3. **Retracts.** `L = (G × G) ⋊ <σ> ∈ B_A`, as a finite-index overgroup of `G × G`
   (`boone-higman-type-a-class-closed-under-finite-extensions`). Embed `G` by
   `g -> (g, r(g))`. Then `σ (g, r(g)) σ^(-1) = (r(g), g)`, which equals `(g, r(g))` iff
   `r(g) = g` iff `g ∈ C`.
4. **Fixed subgroups.** In `G ⋊_α <t>`, `t g t^(-1) = α(g)`. So `C_G(t) = Fix(α)`.
5. **Intersections.** `G` embeds diagonally in `L_1 × L_2`, and
   `C_G((m_1, m_2)) = C_G(m_1) ∩ C_G(m_2)`.

**Decidability.** If `G` is finitely generated and `C = C_G(m)`, then `g ∈ C` iff
`[g, m] = 1` in the finitely generated subgroup `<G, m>` of `L`. That subgroup has
solvable word problem (`type-a-action-gives-boone-higman-for-subgroups`). `∎`
