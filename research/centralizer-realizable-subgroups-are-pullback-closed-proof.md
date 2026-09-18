---
rg: 2
id: centralizer-realizable-subgroups-are-pullback-closed-proof
kind: route
title: Lamp at a point of a type (A) actor, a graph embedding into G × L_Q for pullbacks, and a finite lamp configuration for finite-index enlargements
target: centralizer-realizable-subgroups-are-pullback-closed
requires:
  - pbh-coset-wreaths-iff-identity-edge-hnns
  - bh-type-a-class-closed-under-permutational-lamp-wreaths
  - boone-higman-type-a-class-closed-under-finite-extensions
  - relative-automorphism-of-fp-simple-mif-group-has-type-a-action
  - pbh-coset-closure-passes-to-finite-index-overgroups
  - pbh-wreath-closure-fails-over-undecidable-stabilizers
---

Lane proof (bh-invent-05, 2026-09-18), elementary, not reviewed. `G ∈ B_A` throughout.
Embeddings are written as inclusions.

**1. Point-stabilizer form.**
- **(⇐)** Let `E ⊇ G` be type (A) on `S`, and `s ∈ S`. The lamp wreath `L = Z/2 ≀_S E` has a
  type (A) action (`bh-type-a-class-closed-under-permutational-lamp-wreaths`), so `L ∈ B_A`,
  and `G ≤ E ≤ L`. Put `m = δ_s`. For `g ∈ G`, `g δ_s g^{-1} = δ_{gs}`, which equals `δ_s` iff
  `gs = s`. So `C_G(m) = G ∩ Stab_E(s)`, which is (e). For a finitely supported colouring `f`,
  use `Z/k ≀_S E` and `m = f`: `g f g^{-1} = f ∘ g^{-1}`, which equals `f` iff `g ∈ Stab_E(f)`.
- **(⇒)** This is the (e) ⟹ (b) step of `pbh-coset-wreaths-iff-identity-edge-hnns-proof`.
  - Given `m ∈ L ⊇ G` with `C_G(m) = C`, embed `L` in a finitely presented simple MIF group
    `M`, and let `Ω = Aut_M(M * F(x, y))` act with type (A) on `Hom_M(M * F(x, y), M) = M × M`
    (`relative-automorphism-of-fp-simple-mif-group-has-type-a-action`).
  - The partial conjugations `π_g` (`x ↦ g x g^{-1}`) embed `G` in `Ω`, and
    `Stab_{π(G)}((m, 1)) = π(C_G(m))`. Take `E = Ω` and `s = (m, 1)`.

**2. Pullback.** Let `L_Q ∈ B_A` contain `Q` and `m'` with `C_Q(m') = D`. Put
`L = G × L_Q`, which is in `B_A` by product closure
(`boone-higman-type-a-class-closed-under-finite-extensions`), and embed `G` by the graph
map `ι(g) = (g, φ(g))`, which is injective in the first coordinate. Put `m = (1, m')`. Then
`ι(g) m ι(g)^{-1} = (1, φ(g) m' φ(g)^{-1})`, which equals `m` iff `φ(g) ∈ C_Q(m') = D`. So
`C_{ι(G)}(m) = ι(φ^{-1}(D))`.

**3. Finite-index enlargement.**
- By part 1 choose `E ⊇ G` type (A) on `S` and `s` with `G ∩ Stab_E(s) = C`. Then
  `C' ∩ Stab_E(s) = C`, so the orbit `F_0 = C'·s` has `[C' : C] < ∞` points.
- In `Z/2 ≀_S E ∈ B_A` let `m = Σ_{x ∈ F_0} δ_x`. For `g ∈ G`, `g m g^{-1} = m` iff
  `g F_0 = F_0`.
- If `g F_0 = F_0` then `gs = c's` for some `c' ∈ C'`. So `c'^{-1} g ∈ G ∩ Stab_E(s) = C ⊆ C'`,
  hence `g ∈ C'`. The converse is clear. So `C_G(m) = C'`.

**4. Intersections.** This is case 5 of `pbh-coset-wreaths-iff-identity-edge-hnns`.

**Consequences.**
- **Normal subgroups:** pull back `D = 1 ∈ R(Q)`, where `1` is finite (case 1 of the cited
  node).
- **`C ⊇ [G, G]`:** pull back `φ(C)` along `φ: G → G^ab`. `G^ab` embeds in `V`, and every
  subgroup of a finitely generated virtually abelian group is in `R`
  (`pbh-coset-closure-passes-to-finite-index-overgroups`, Applications), and
  `C = φ^{-1}(φ(C))` because `ker φ ⊆ C`.
- **Relative versions:** these are part 2 verbatim.
- **Finite-index subgroups:** pull back along the finite quotient `G → G/core(C)`, in which
  every subgroup is finite, hence in `R`.
- **Mihailova dichotomy.**
  - `r(a, b) = (a, a)` is a homomorphism `Q × Q → Q × Q` fixing `Δ_Q` pointwise, so
    `Δ_Q ∈ R(Q × Q)` by the retract case of the cited node. `Q × Q ∈ B_A` by product
    closure. Part 2 applies to `π × π`.
  - The map `(u, v) ↦ π(u) π(v)^{-1}` is constant exactly on the cosets of `P_Q`, since
    `π(ua) π(vb)^{-1} = π(u) π(v)^{-1}` when `π(a) = π(b)`. It is `F × F`-equivariant for the
    left-right action. So condition (a) for `P_Q` is the left-right lamplighter.
  - The undecidable half is the cited refutation node. ∎
