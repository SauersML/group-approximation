---
rg: 2
id: al-local-to-global-holds-without-vertex-transitivity
kind: claim
title: Amir–Lazarovich's local-to-global theorem needs no vertex-transitivity when its 2-ball condition is imposed at every vertex; a subgroup G of U(Alt_{2d-1}) with G_v|_{B_2(v)} = U_v|_{B_2(v)} for all vertices v has closure containing the simple group U^+, so for a cocompact G density is a finite check
requires:
  - twisted-davis-amalgams-keep-hyperplane-data
---

**ESTABLISHED** (lane re-reading of Amir–Lazarovich's proof, not reviewed). The mathematics is AL's
(arXiv:2605.09493, §4, l.922–1680, Theorem "local to global" l.113). We only observe that their
argument runs with the hypothesis at every vertex in place of vertex-transitivity.

## Statement

Let `d >= 6`, `X = X_{O_d}` and `U = U(Alt_{2d-1})`. Let `G ≤ U` be any subgroup such that

  **(3∀)** `G_v|_{B_2(v)} = U_v|_{B_2(v)}` for every vertex `v` of `X`.

Then `cl(G_v) = U_v` for every `v`, and `cl(G) ⊇ U^+`. So `cl(G)` is `U^+` or `U`; it is just
non-compact, and it has no nontrivial discrete normal subgroup.

If `G` has finitely many orbits on vertices, then (3∀) is a finite check: one 2-ball per orbit
representative.

## Proof

1. **Where AL use transitivity.** AL prove (3) ⟹ (1) by induction on `n`, with `P(n)` the statement
   `G_v|_{B_n(v)} = U_v|_{B_n(v)}`.
   - Vertex-transitivity is used explicitly once, at l.1048: "it suffices to show `cl(G_v) = U_v` for
     some fixed `v`".
   - Implicitly, it transports hypotheses between vertices. The places we found are:
     - the induction hypothesis at a neighbour `v̄` of `v`, in Claim "Reduction to paths", Case 1
       (l.1183–1184, `G^{n-1}_{v̄}|_{B_1(x)} = U^{n-1}_{v̄}|_{B_1(x)}`) and Case 2 (l.1233);
     - the local action `D_x(G_x) = Alt_ℓ` at an arbitrary vertex `x`, in Claim "non trivial implies alt"
       (l.1115), together with the 2-ball control of `Fix_G(S)` at `x`.
   - The other uses of the induction hypothesis (l.1067, 1294, 1576, 1672) are at `v` itself.
   - A search of l.1030–1680 finds no other occurrence of transitivity.
2. **Run the induction at all vertices at once.** Replace `P(n)` by `P∀(n)`: `P(n)` for every vertex.
   - (3∀) gives `P∀(1)` and `P∀(2)`, and it gives `D_x(G_x) = Alt_ℓ` and the `Fix_G(S)` statement at
     every `x`.
   - In AL's step `P(n) ⟹ P(n+1)` at `v`, every hypothesis invoked is `P(n)` at `v` or at a neighbour
     `v̄`, since `G^{n-1}_{v̄}|_{B_1(x)}` with `x ∈ B_{n-1}(v̄)` is controlled by `P(n)` at `v̄`.
   - So `P∀(n) ⟹ P∀(n+1)` by AL's argument verbatim, and `cl(G_v) = U_v` for all `v`.
3. **From stabilizers to `U^+`.**
   - `N := ⟨U_v : v ∈ X^0⟩` is open and normal in `U`, since `U` permutes the stabilizers.
   - `U_v ⊆ U^+`, because fixing a vertex preserves the proper 2-coloring of `X^0`. By AL (l.807–812),
     `U^+` is exactly the coloring-preserving part of `U` and has index 2.
   - `U^+` is simple (AL Prop. l.897) and `N ≠ 1`, so `N = U^+`. Hence `cl(G) ⊇ N = U^+`.
   - Just non-compactness and the absence of discrete normal subgroups are the arguments of
     `twisted-davis-amalgams-keep-hyperplane-data` item 1.

## Consequence for Kourovka 21.46

For the twisted amalgams `G = ⟨W_{F_a}, φ W_{F_b} φ^{-1}⟩`, whose projection has finitely many orbits
because it contains a lattice, condition (N1) is now the finite check (3∀). By item 1 of the required
node this gives faithfulness on the tree for free. The remaining conditions are:
- **(DENS-fin)** exhibit `ε` (a wall twist) and verify (3∀) at the finitely many orbit representatives,
  a bounded computation of 2-ball local actions of short words;
- **(N2)** a boundary-2-transitive tree closure. An all-vertex form of Burger–Mozes' Lemma 3.5.3
  (quoted by AL at l.924) plausibly reduces this to a finite check too; not examined.

## Lesson for general BH

- **Transitivity was a convenience.** Local-to-global density theorems for universal groups are really
  statements about *all* vertices. Vertex-transitivity only lets one check a single vertex.
- **Cocompact is enough.** For cocompact candidates (lattice-generated subgroups), density becomes a
  finite local certificate.
- **The certificate carries the proof.** Combined with density-implies-faithfulness, simplicity of a
  lattice-built host reduces to one finite computation plus the non-residually-finite input. The
  input is cheap, since it can be imported through a hyperplane.
