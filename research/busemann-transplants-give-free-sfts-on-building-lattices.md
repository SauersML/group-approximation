---
rg: 2
id: busemann-transplants-give-free-sfts-on-building-lattices
kind: claim
title: Corner-deterministic strongly aperiodic Z^r-SFTs transplant along Busemann coordinates to free SFTs over building lattices; with Kari–Papasoglu tiles, every simply-transitive rank-2 building lattice with an SFT boundary shift carries a strongly aperiodic SFT
distinct_from:
  euclidean-building-boundary-shifts-are-quantum-rigid: that is the undecorated boundary shift X_Ω, which is minimal but only topologically free; this decorates it with a Busemann Z^r-fibre and makes it free, keeping finite type.
  deterministic-time-lifts-inherit-quantum-rigidity: that lifts along a deterministic TIME factor of a product group; this lifts along a deterministic CONE direction of the building's own boundary, with no product structure.
  thick-building-flat-sfts-are-never-quantum-rigid: that codes the building over its translation lattice Z^d and is never rigid; this codes Z^r-data over the lattice Γ acting on its boundary, where branching is absorbed by determinism.
  free-minimal-triangle-permutive-sft-exists: that needs triangle-permutivity (three-way determinism) over Z^2; this needs only one-corner determinism, which Kari–Papasoglu supply, and gains non-amenability.
---

**ESTABLISHED, conditional on (H_Ω)** (lane bh-invent-04, 2026-09-18; lane proof, not reviewed, no
priority claimed). (H_Ω) is the finite-type half of the open node
`euclidean-building-boundary-shifts-are-quantum-rigid`: *the boundary shift `X_Ω ⊆ 𝒜^Γ` is an SFT over `Γ`*.
Kari–Papasoglu (GAFA 1999, 4-way deterministic aperiodic tile sets) is recalled, not re-read.

## Setting

- `Δ` is a locally finite thick Euclidean building of rank `r`. `Γ ≤ Aut(Δ)` is torsion-free and
  type-preserving, and acts simply transitively on the special vertices `V_0` of one type, with base
  vertex `o`. Examples: the index-3 type-preserving subgroups of the torsion-free CMSZ `Ã₂` groups
  (which act simply transitively on all vertices).
- `c ∈ Ω`. `Q(v,c)` is the sector at `v ∈ V_0` toward `c`. `b_c: V_0 → L ≅ Z^r` are the Busemann
  coordinates of `chamber-fixing-building-lattice-elements-translate-horospheres`, and `C̄` is the
  closed positive cone.
- **Radius-K sector coding.** `x_c(γ) = γ^{-1}·(Q(γo, c) ∩ B(γo, K))` is a subset of the finite ball
  `B(o,K)`. This is `Γ`-equivariant and refines the germ coding of `X_Ω`, so it is a conjugate
  subshift `X_Ω^K`, and (H_Ω) is conjugacy invariant. For `v ∈ V_0` and `ℓ ∈ L ∩ C̄` with `|ℓ| ≤ K`,
  let `p_ℓ(v)` be the vertex of `Q(v,c)` with `b_c = b_c(v) + ℓ`. It is read off the symbol at `v`.
- **Decoration.** `Y ⊆ A^{Z^r}` is an SFT that is *corner-deterministic*: there is `G` with
  `y(z) = G(y(z+e_1), …, y(z+e_r))` for all `y ∈ Y` and `z`.
- **Embedding.** Fix an isomorphism `M: Z^r → L` with every `M e_i` in the **open** cone. Such an `M`
  exists: take a basis `{u, v_2, …, v_r}` of `L` with `u` primitive and interior, then replace `v_i` by
  `v_i + N u` for large `N`.

## Statement

Put `Y_Δ = {(x_c, R∘M^{-1}∘b_c) : c ∈ Ω, R ∈ Y} ⊆ (𝒜_K × A)^{V_0} = (𝒜_K × A)^Γ`.

1. **Skew product.** `Y_Δ` is a `Γ`-subshift. The map `(c, R) ↦ (x_c, R∘M^{-1}∘b_c)` conjugates the
   Busemann skew product `Ω ×_β Y` (with `L` acting on `Y` through `M`) to it.
2. **Finite type (given H_Ω).** Take `K` at least the radius needed for `M` of a window of `Y`'s rules
   and of `{e_i}`. Then `Y_Δ` is exactly the set of configurations `(g, t)` satisfying three local rules:
   - (R1) `g ∈ X_Ω^K`;
   - (R2) at each `v`, the pattern `w ↦ t(p_{Mw}(v))` on a translate `W' ⊂ M^{-1}C̄` of each forbidden
     window avoids `Y`'s forbidden patterns;
   - (R3) `t(v) = G(t(p_{Me_1}(v)), …, t(p_{Me_r}(v)))`.
   So `Y_Δ` is an SFT over `Γ`.
3. **Freeness.** `Γ ↷ Y_Δ` is free if and only if `Y` has no periodic point with a period in
   `M^{-1}{τ_c(γ)}`. It is free whenever `Y` is strongly aperiodic. For cocompact rank-2 `Γ`, periodic
   flats show that the converse also holds: any periodic point of `Y` destroys freeness.
4. **Kari–Papasoglu corollary (r = 2).** Kari–Papasoglu's 4-way deterministic aperiodic Wang tile set is
   NE-deterministic, since a tile is determined by its north and east colours. Its tiling SFT has no
   periodic point: a singly periodic point of a `Z²`-SFT forces a doubly periodic one. So under (H_Ω),
   **every such rank-2 lattice `Γ` carries a strongly aperiodic SFT**. This includes Kazhdan,
   one-ended, non-amenable CMSZ `Ã₂` groups: first their type-preserving subgroups, then the groups themselves,
   since existence of strongly aperiodic SFTs is a commensurability invariant (Carroll–Penland, recalled).
5. **Programmability.** Any corner-deterministic `Z^r`-SFT can be used. Lukkarila's 4-way deterministic
   simulations of reversible Turing machines (recalled) give decorations whose languages encode
   computations, so the transplanted SFT inherits them.

## Proof

1. **Equivariance.**
   - `x_{hc}(γ) = x_c(h^{-1}γ)`.
   - `b_c(h^{-1}w) − b_{hc}(w)` is a constant lying in `L = M Z^r`.
   - So `h` sends `(x_c, R∘M^{-1}b_c)` to `(x_{hc}, (σ^{M^{-1}β} R)∘M^{-1}b_{hc})`.
   - The map is continuous and injective, since `c` is read off `x_c`, and `R` is recovered because
     `b_c(V_0)` is a full coset of `L`.
2. **Finite type.**
   - *Necessity.* Points of `Y_Δ` satisfy R1–R3: on `Q(v,c)`, which lies in an apartment, `b_c` is an
     isometric coordinate.
   - *Sufficiency.* Let `(g,t)` satisfy R1–R3. By R1 and (H_Ω), `g = x_c` for a unique `c`.
   - *Nesting.* `p_{ℓ}(p_{ℓ'}(v)) = p_{ℓ+ℓ'}(v)`, because `Q(u,c) ⊆ Q(v,c)` is the subcone `b_c(u) + C̄`
     for `u ∈ Q(v,c)`.
   - *Iteration.* Iterating R3 `k` times gives `t(v) = G^{(k)}(t(p_{Mw}(v)) : w ∈ N^r, |w|_1 = k)`.
   - *Coherence.* Suppose `b_c(v) = b_c(v')`. Pick a special vertex `u` with `Q(u,c) ⊆ Q(v,c) ∩ Q(v',c)`.
     - Since `conv{Me_i}` is a compact subset of the open cone, `Mw` lies at distance at least `δk` from
       `∂C` for `|w|_1 = k`.
     - So for `k ≫ 0`, `b_c(v) + Mw ∈ b_c(u) + C̄`.
     - Hence `p_{Mw}(v)` and `p_{Mw}(v')` are the same vertex: the unique point of `Q(u,c)` with that
       coordinate.
     - So `t(v) = t(v')`, i.e. `t = R̃∘b_c` for a function `R̃` on `L`.
     - This is where **openness of the cone matters**: branching of the building beyond the common
       subsector is invisible to `G^{(k)}`.
   - *Conclusion.* Put `R = R̃∘M`. R2 says every `Y`-window of `R` is legal, so `R ∈ Y`, and
     `(g,t) = (x_c, R∘M^{-1}b_c)`.
3. **Freeness.** `γ` fixes `(c, R)` if and only if `γc = c` and `σ^{M^{-1}τ_c(γ)}R = R`. For `γ ≠ 1`,
   `τ_c(γ) ≠ 0` (`chamber-fixing-building-lattice-elements-translate-horospheres`). The converse is the
   periodic-flat argument of that node.
4. **Kari–Papasoglu.** Immediate from 2 and 3.
5. **Programmability.** Immediate from 2. ∎

## What this does and does not give for the master route

- **Gives, for gate G2's free part over non-amenable Kazhdan `Γ`:** a free SFT over `Γ`, conditional only
  on (H_Ω).
  - *Minimality* is not claimed. Skew products over minimal `Ω` with minimal fibre need not be minimal,
    and Kari–Papasoglu tilings are not known to be minimal.
  - *Quantum rigidity* is the open node `busemann-transplants-of-rigid-z2-sfts-are-quantum-rigid`, which
    reduces it to rigidity of `X_Ω` and of `Y` plus one centrality statement.
- **Coupling.** For a general input, `Γ` is the `H`-factor of `Λ = Λ_0 × Γ`. With
  `deterministic-time-lifts-inherit-quantum-rigidity`, an action of `Λ_0` on `Y_Δ` by cellular automata,
  jointly free and minimal, would give (★).

## Lesson for general BH

- **Transfer principle ("Busemann transplant").**
  - Every construction over `Z^r` that is deterministic from an **interior** cone direction transfers to
    lattices in rank-`r` Euclidean buildings.
  - Rank-2 lattices that are Kazhdan, one-ended and non-amenable thereby inherit what `Z²` offers:
    strong aperiodicity, and computation via deterministic tiles.
  - Freeness transfers because chamber stabilizers embed in `Z^r` through Busemann translation.
  - Coherence across the building's branching is exactly **cone-interior determinism**; any
    non-deterministic decoration fragments across branches.
- **Consequence for G2.** G2 over non-amenable one-ended `Γ` reduces to four inputs:
  - a corner-deterministic, rigid, strongly aperiodic `Z²`-SFT;
  - (H_Ω);
  - rigidity of `X_Ω`;
  - one centrality step.
- **Programmability.** Deterministic computing tiles (Kari–Papasoglu, Lukkarila) supply the
  programmable decoration; determinism is what keeps the coding rigid-compatible.
