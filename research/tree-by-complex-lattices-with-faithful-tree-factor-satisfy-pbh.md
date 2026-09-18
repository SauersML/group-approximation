---
rg: 2
id: tree-by-complex-lattices-with-faithful-tree-factor-satisfy-pbh
kind: claim
title: A uniform lattice in Aut(T) × Aut(Y) that acts faithfully on the tree T lies in B_A; in particular the Amir–Lazarovich lattices satisfy the permutational Boone–Higman property
distinct_from:
  product-of-trees-lattices-with-faithful-factor-satisfy-pbh: that treats products of trees only; here the second factor Y is any simply connected locally finite complex, such as a right-angled Davis complex, and only the tree factor has to be faithful.
  product-of-two-trees-lattices-satisfy-permutational-boone-higman: that uses commensurability of vertex groups with F_2 and needs no faithfulness; here the vertex groups are lattices on Y, with no commensurability class assumed, and faithfulness is supplied by just-infiniteness.
  amir-lazarovich-lattice-torsion-is-square-diagonals: that reduces the torsion question for the Amir–Lazarovich lattices; this places the same lattices, and all their subgroups and finite products, in B_A.
artifacts:
  - research/artifacts/gq-bh-bh-testcases-ranking.md
---

**ESTABLISHED** (lane proof, a direct application of BLIW's tree method via
`faithful-finite-index-graphs-of-groups-have-type-a-overgroups`; not independently
reviewed; no priority claimed).

## Statement

`B_A` is the class of `boone-higman-type-a-class-closed-under-finite-extensions`.

1. **General criterion.** Let `T` be a locally finite tree, and `Y` a simply connected,
   locally finite cell complex. Let `Γ ≤ Aut(T) × Aut(Y)` act on `T × Y` properly and
   cocompactly by cellular automorphisms. If the projection `pr_T : Γ → Aut(T)` is
   injective, then `Γ ∈ B_A`.
2. **Faithfulness from just-infiniteness.** If `Γ` is just-infinite (every nontrivial
   normal subgroup has finite index) and `pr_T(Γ)` is infinite, then `pr_T` is injective.
3. **Amir–Lazarovich lattices.** Let `Λ' ≤ Aut(T_c) × Aut(X_(O_d))` be a lattice from the
   proof of Theorem A of Amir–Lazarovich, arXiv:2605.09493. Then `Λ' ∈ B_A`.
   - So `Λ'`, its finitely presented simple finite-index subgroup `Λ`, and every
     subgroup of either satisfy the permutational Boone–Higman property.
   - Every finite direct product `Λ'^k`, and every product of `Λ'` with other members of
     `B_A`, embeds in a finitely presented simple group.

Item 3 is new information even though `Λ` is itself finitely presented and simple.
Boone–Higman is not known to be closed under direct products
(`boone-higman-closed-under-finite-direct-products`, OPEN), so `Λ × Λ` was not known to
embed. Neither was `Λ'`: it is virtually simple, not residually finite, and has torsion.

## Proof

**Item 1.**
- **Vertex stabilizers are finitely presented.** For `v ∈ V(T)`, the stabilizer `Γ_v`
  preserves `{v} × Y ≅ Y`.
  - Cell stabilizers of `Γ_v` on it are contained in cell stabilizers of `Γ` on `T × Y`, so
    they are finite.
  - If `g({v} × σ) = {v} × σ'` then `g ∈ Γ_v`. So distinct `Γ_v`-orbits of cells `{v} × σ` lie
    in distinct `Γ`-orbits of cells of `T × Y`, and there are finitely many.
  - So `Γ_v` acts properly and cocompactly on the simply connected, locally finite complex
    `Y`, and is therefore finitely presented. This is the standard fact, not re-read.
- **Edge stabilizers are finitely presented.** The pointwise stabilizer of an edge `e`
  at `v` has finite index in `Γ_v`, because `Γ_v` permutes the finitely many neighbours of
  `v`. So it is finitely presented.
- **Apply the tree criterion.** Pass to the barycentric subdivision `T'` of `T`, on which
  `Γ` acts without inversions.
  - `T'` is locally finite and `Γ` has finitely many orbits of vertices on it, by
    cocompactness.
  - The stabilizer of an edge `[v, m_e]` of `T'` is the pointwise stabilizer of `e`.
  - `Γ` acts faithfully on `T'` because it does on `T`.

  Item 2 of `faithful-finite-index-graphs-of-groups-have-type-a-overgroups` gives
  `Γ ∈ B_A`.

**Item 2.** The kernel of `pr_T` is normal. If it were nontrivial it would have finite
index, and `pr_T(Γ)` would be finite.

**Item 3.** Proof of Theorem A in the TeX source (MSI `bhfe/al/main.tex`, l.2347–2383, read
2026-09-18). There, `Λ'` is an irreducible lattice in `Aut(T_c) × Aut(X_(O_d))`, with
`c, d ≥ 6`, and:
- "`pr_(T_c)(Λ')` and `pr_(X_(O_d))(Λ')` are vertex transitive on `T_c` and `X_(O_d)`
  respectively";
- "By Bader-Shalom, `Λ'`, and any of its finite index subgroups, is just-infinite";
- `Λ'` acts simply transitively on the vertices of `T_c × X_(O_d)`, by the proposition "the
  lattice Lambda", l.1807, as recorded in `research/artifacts/gq-bh-bh-free-extensions-cd3-sources.md`.

`X_(O_d)` is the Davis complex of a right-angled Coxeter group on a finite graph, so it is
CAT(0), hence simply connected, and it is locally finite.
- The action on `T_c × X_(O_d)` is proper, being free on vertices, and cocompact, with one
  vertex orbit.
- `pr_(T_c)(Λ')` is vertex-transitive on the infinite tree `T_c`, so it is infinite.
- By item 2, `pr_(T_c)` is injective, and item 1 gives `Λ' ∈ B_A`.
- The remaining assertions are items 1–3 of
  `boone-higman-type-a-class-closed-under-finite-extensions`. ∎

## Scope

- Item 1 needs a **faithful tree factor**. It says nothing about lattices on
  products without a tree factor, such as exotic Ã₂ lattices
  (`exotic-a2-lattices-satisfy-boone-higman`), or about Kazhdan groups such as
  `Q_(g,2)` or Deligne's lattice, which have no unbounded tree actions.
- Without faithfulness, the kernel of `pr_T` is a normal subgroup contained in every
  vertex stabilizer `Γ_v`. For just-infinite `Γ`, item 2 removes it. In general it is the
  gap described in `product-of-trees-lattices-satisfy-permutational-boone-higman`,
  Attempt 3, now for arbitrary second factors.
