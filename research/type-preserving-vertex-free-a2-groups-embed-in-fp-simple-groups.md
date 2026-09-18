---
rg: 2
id: type-preserving-vertex-free-a2-groups-embed-in-fp-simple-groups
kind: claim
title: Every group acting freely, type-preservingly and with finitely many orbits on the vertices of a thick Ã₂ building embeds in a finitely presented simple group, through the period-3 Robertson–Steger 2-graph restricted to phase 0 and a skew product over the index-3 degree lattice
distinct_from:
  type-transitive-vertex-free-a2-groups-embed-in-fp-simple-groups: that is the case where the type-rotation character is nonzero, where the transition matrices are primitive; this is the type-preserving case, where they have period 3 and the primitive-aperiodic embedding theorem does not apply as stated.
  primitive-aperiodic-two-graph-full-groups-embed-in-fp-simple: that needs primitive matrices; this reruns its proof on the phase-0 reduction, with the skew-product group L/nZ² in place of (Z/n)².
artifacts:
  - research/artifacts/gq-bh-bh-groupoid-frontier.md
---

**ESTABLISHED** (lane proof, bh-groupoid 2026-09-18, inline below; not independently
reviewed; no novelty claimed).

## Statement

Let `B` be a locally finite thick Ã₂ building, and `Γ` a group of type-preserving
automorphisms acting freely on the vertices with finitely many orbits. Then `Γ` embeds in an
infinite simple group of type `F_∞`.

Together with `type-transitive-vertex-free-a2-groups-embed-in-fp-simple-groups`, this proves
`vertex-free-type-rotating-a2-groups-satisfy-boone-higman`.

## Proof

Notation is as in `primitive-two-graph-fp-simple-embedding-proof`, with `Λ = Λ_Γ` and `c`
the degree cocycle.
- The *phase* of a tile is its base type.
- `L = {(a,b) ∈ Z² : a + 2b ≡ 0 mod 3}`, a subgroup of index 3.
- `X_0 = ⊔_{phase(v)=0} Z(v)`.

1. **Phases and degrees.**
   - By `a2-rs-matrices-irreducible-and-primitive-iff-type-transitive`, `M_1` and `M_2`
     are irreducible of period 3, with the phases as cyclic classes. `M_1` raises the phase
     by 1 and `M_2` by 2.
   - So every path of degree `(a,b)` raises the phase by `a + 2b`.
   - `M_j^3` is primitive on each phase. So there is `K` such that between any vertices
     `u, v` there are paths of every degree `(a,b) ≥ (K,K)` with
     `a + 2b ≡ phase(v) − phase(u) (mod 3)`. To build one, take a colour-1 path to an
     intermediate vertex of the right phase, then a colour-2 path.
2. **Γ lives on X_0.**
   - Put `phase(O) = 0`. The decorations sit at `O`, so `Y ⊆ X_0`.
   - By `a2-group-embeds-in-rs-two-graph-geometric-proof`, `Γ ≤ [[G_Λ|_{X_0}]]`, extending
     by the identity on `X_0 \ Y`.
   - For `x, y ∈ X_0` with `σ^p x = σ^q y`, the phases of `x(p) = y(q)` give
     `p − q ∈ L`. So `c(G_Λ|_{X_0}) ⊆ L`.
3. **Rescaling.** Fix `n = 3m`, with `m` so large that `M_j^n(a,a) ≥ 2` for all `a` and
   `j`, and `n ≥ K`. This is possible because each diagonal block of `M_j^n` is primitive
   with Perron value `q^{2n} → ∞`.
   - `Λ^(n)` has at least two loops of each colour at every vertex.
   - `G_{Λ^(n)} ≅ c^{-1}(nZ²)` (Step 1 of the reference proof).
   - Aperiodic points stay aperiodic. `Λ` is aperiodic by
     `rs-two-graph-aperiodicity-from-h3-and-irreducibility`.
4. **Skew product over T = L/nZ².** Let `H = G_Λ|_{X_0} ×_c̄ T`, where `c̄` is `c` modulo
   `nZ²`. This is well defined by item 2.
   - `H|_{X_0×{0}} ≅ c^{-1}(nZ²)|_{X_0} = G_{Λ^(n)}|_{X_0}`.
   - `f ↦ f × T` embeds `[[G_Λ|_{X_0}]]` in `[[H]]` (Step 2 of the reference proof).
5. **Compression into X_0 × {0}.** Rerun Step 3 of the reference proof, with every path
   `ρ_{v,a}` of degree `R` having range of phase 0, and at least one such path left over.
   - For `v` of phase 0 and `a ∈ T`, choose `σ_{v,a}` from `s(ρ_{v,a})` to `v`, of degree
     `≥ (K,K)` and `≡ −a − R (mod nZ²)`.
   - Both sides lie in the coset forced by item 1: `R + d(σ) ∈ L` and `a ∈ L`. So such
     paths exist.
   - The bisections `ψ_{v,a}` then compress `X_0 × T` properly into `X_0 × {0}`.
   - So `[[G_Λ|_{X_0}]] ↪ [[G_{Λ^(n)}|_{X_0}]]`.
6. **Product with the full 2-shift, and F_∞.** Put `Λ' = Λ^(n) × B_2` and
   `Y' = X_0 × {0,1}^N`, a union of vertex cylinders of `Λ'`.
   - `f ↦ f × id` embeds `[[G_{Λ^(n)}|_{X_0}]]` in `S = [[G_{Λ'}|_{Y'}]]`, using
     `finite-k-graph-boundary-groupoid-standard-facts`, item 2.
   - By `li-finite-k-graph-full-groups-are-f-infinity`, with `Y_v = Z(v)` for `v` of
     phase 0 and `Y_v = ∅` otherwise, `S` is of type `F_∞`. Every vertex of `Λ'` has two
     loops of each colour.
7. **Purely infinite, minimal, essentially principal.** As in Step 6 of the reference proof,
   inside `Y'`.
   - The needed paths stay inside phase 0, because degrees in `nN²` preserve phase, and the
     phase-0 block of `Λ^(n)` is strongly connected.
   - Aperiodic points are dense (standard facts, item 4).
8. **Homology and simplicity.**
   - `G_{Λ'}|_{Y'} = G_{Λ^(n)}|_{X_0} × G_2`, so by
     `matui-groupoid-homology-kunneth-and-full-shift-vanishing` its homology vanishes.
   - Then Li's exact sequence (`li-ah-exact-sequence-for-minimal-comparison-groupoids`)
     makes `S` perfect.
   - Matui (`matui-purely-infinite-minimal-full-groups-have-simple-d`) makes `S = D(S)`
     simple. `S` is infinite.

Composing items 2, 4, 5 and 6 embeds `Γ` in `S`. ∎

## Remark

The reference proof uses primitivity only for two things: paths of every large degree
(Steps 0 and 3), and minimality (Step 6). With period 3, both survive after restricting to
one phase and replacing `Z²` by the lattice `L` of phase-preserving degrees.
