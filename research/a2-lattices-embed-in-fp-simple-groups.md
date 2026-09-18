---
rg: 2
id: a2-lattices-embed-in-fp-simple-groups
kind: claim
title: Every discrete cocompact group of automorphisms of a locally finite thick Ã₂ building, with or without torsion, exotic or not, embeds in a finitely presented simple group of type F_∞
distinct_from:
  vertex-free-type-rotating-a2-groups-satisfy-boone-higman: that is the case of free type-rotating actions on vertices, through the Robertson–Steger 2-graph; this removes both freeness and type rotation, replacing the 2-graph by an orbit category with finite unit groups (the vertex stabilizers) and using Li's theorem for categories with invertibles.
  exotic-a2-lattices-satisfy-boone-higman: that is the exotic case of this statement, which this proves (lane proof).
artifacts:
  - research/artifacts/gq-bh-bh-groupoid-frontier.md
---

**ESTABLISHED** (lane proof, bh-groupoid 2026-09-18, below; not independently reviewed; no
priority claimed). Step 5 reruns Steps 1–8 of `primitive-two-graph-fp-simple-embedding-proof`, and
`type-preserving-vertex-free-a2-groups-embed-in-fp-simple-groups` in the type-preserving
case. The only change is that the Kumjian–Pask groupoid is replaced by the groupoid `𝒢_Γ`
of Step 2. Every point where the change matters is written out.

## Statement

Let `B` be a locally finite thick Ã₂ building of order `q ≥ 2`, and `Γ ≤ Aut(B)` discrete
and cocompact. Then `Γ` embeds in an infinite simple group of type `F_∞`.

Examples:
- the Tits–Ronan chamber-regular lattices, two of which are exotic;
- the panel-regular lattices of Ronan–Kantor–Essert, whose exotic members form BCL's
  infinite family (Corollary `cor:ExistenceExotic`);
- Barré's lattice;
- every CMSZ group;
- every lattice in `PGL_3(D)`.

## Step 0. Reductions

- **(R1) Finite extensions.** Let `𝒢` be a purely infinite minimal ample groupoid on a Cantor
  set `X` with `S = F(𝒢)`. Let `Γ_0 ≤ Γ` have finite index with `Γ_0 ≤ S`. Then `Γ ↪ S`.
  - Let `N` be the normal core of `Γ_0`, with `r = [Γ:N]`. Then
    `Γ ↪ N ≀ Sym(r) ≤ F(𝒢 × R_r)`, where `R_r` is the pair groupoid on `r` points
    (Kaloujnine–Krasner).
  - Pure infiniteness gives disjoint clopen sets `U_1, …, U_r ⊆ X` and bisections
    `X → U_i`. These conjugate `𝒢 × R_r` onto `𝒢|_{⊔U_i}`.
  - Extending by the identity embeds `F(𝒢|_{⊔U_i})` in `F(𝒢)`.
- **Type-rotating subgroup.** The type-rotating subgroup has index at most 2, and the hosts
  built below are of the form in (R1). So we may assume `Γ` is type rotating.
- **Stabilizers.** Vertex stabilizers are finite, by discreteness and local finiteness.
  Since `Γ` acts faithfully, finitely many vertex orbits give a uniform `R_0` with
  `Fix_Γ(Ball_{R_0}(z)) = 1` for every vertex `z`: a decreasing chain of subgroups of a
  finite group stabilizes.

## Step 1. The orbit category ℭ_Γ

Notation for tiles, parallelograms and the maps `o` and `t` follows RS §7.
- Choose representatives `i_a` of the tile classes `a ∈ A = Γ\𝔗`, and let
  `K_a = Stab_Γ(i_a)`, which is finite.
- A morphism `a ← b` is a pair `(p, γ)` with `p ∈ 𝔓`, `o(p) = i_a` and `γ i_b = t(p)`. Its
  degree is the shape of `p`.
- Composition is `(p,γ)(p',γ') = (p ∪ γp', γγ')`, and it is associative.

Properties:
- **Cancellation.** `ℭ_Γ` is left and right cancellative. For right cancellation, compare
  `γ` and then the initial parts of the common shape.
- **Units.** The units are `(i_a, k)` with `k ∈ K_a`, and they are exactly the morphisms of
  degree 0.
- **(UFP\*).** Split `P` at shape `m` as `p ∪ g p'`, where `g i_b = t(p)`. The element `g` is
  unique up to `K_b`.
- **Local finiteness.** Each object has finitely many morphisms of each degree.
- **Disjoint minimal common multiples up to units.** A common extension of `p` and `p'` from
  `i_a` is unique when it exists. At each corner, the closing chamber is unique because the
  flag graph of the link, a projective plane, has girth 6. So `cℭ ∩ dℭ` is a finite
  (possibly empty) disjoint union `⊔εℭ`, and every element of `I_l` is a finite disjoint
  union of maps `cd^{-1}` (as in `finite-k-graph-standard-facts-proof`, Lemma A).

`ℭ_Γ` is therefore a cancellative, finitely aligned category with an `N²`-valued degree map
satisfying (UFP\*). It has finitely many objects and finite unit groups `ℭ^*(a,a) = K_a`.

## Step 2. The groupoid 𝒢_Γ

**Unit space.**
- Let `𝒮_a` be the set of type-rotating isometric embeddings of the model quarter-plane
  whose first tile is `i_a`, and `𝒮 = ⊔_a 𝒮_a`, with the cylinder topology.
- Each `𝒮_a` is compact and homeomorphic to a clopen subset of the boundary `Ω`, as in
  Claim 1 of `a2-group-embeds-in-rs-two-graph-geometric-proof`.

**Arrows.** `𝒢_Γ` is the set of quadruples `(S', n, g, S)` with `S, S' ∈ 𝒮`, `n ∈ Z²`, `g ∈ Γ`, and `S'(l+n) = g·S(l)` for all large `l`.
- Composition: `(S'',n',g',S')(S',n,g,S) = (S'', n+n', g'g, S)`.
- Basic open bisections: `{(p ∪ γτ, d(p) − d(p'), γγ'^{-1}, p' ∪ γ'τ)}`, one for each pair of
  morphisms `(p,γ)`, `(p',γ')` with a common source, as `τ` ranges over `𝒮_b`.

**Lemma 2.1: 𝒢_Γ is Li's groupoid.** `𝒢_Γ ≅ I_l(ℭ_Γ) ⋉ ∂Ω`, and `∂Ω ≅ 𝒮`.

*Proof.*
- **The unit space.** Maximal characters are the infinite chains of morphisms, modulo
  units, whose degrees tend to infinity. These are the sectors in `𝒮`.
  - The argument is that of `finite-k-graph-standard-facts-proof`, item 1, using Li's Lemma
    `lem:infpaths` and Lemma `lem:Omegamax` (arXiv:2110.04501, read at source).
  - `𝒮` is compact, so `∂Ω = Ω_max ≅ 𝒮`.
- **The map.** Send the germ `[(p,γ)(p',γ')^{-1}, p' ∪ γ'τ]` to
  `(p ∪ γτ, d(p) − d(p'), γγ'^{-1}, p' ∪ γ'τ)`.
- **Well defined.** Germ equality means the two maps agree on a principal ideal. In `ℭ_Γ`
  morphisms record `γ` exactly, so the lag and the element agree.
- **Injective.** Suppose two germs at `S` have the same `(n, g)`. On the ideal generated by
  a deep prefix `(P, η)` of `S`, both send `(P,η)` to (initial part of `S'` of shape
  `d(P)+n`, `gη`).
- **Surjective.** Given `(S', n, g, S)`, take `p'` a deep prefix of `S` with `γ'`, then `p`
  the prefix of `S'` of shape `d(p') + n`, and `γ = gγ'`.
- **Homeomorphism.** Basic sets correspond. ∎

**Lemma 2.2: Hausdorff.** Li's Lemma `lem:HdOmega`(i) (read at source) requires every fixed
set `{x : s(x) = x}` to be a finite union of constructible ideals.
- By right cancellation, `cd^{-1}` fixes `x = dy` iff `c = d`.
- So the fixed set of a disjoint union of maps `cd^{-1}` is the union of those `dℭ` with
  `c = d`. ∎

## Step 3. Γ inside the full group

Let `D` be the tiles based at `O`. For `d ∈ D` write `d = g_d i_{a(d)}`.
- The boundary splits as `Ω = ⊔_{d∈D} Ω(d)`, and `Ω(d) ≅ 𝒮_{a(d)}` via
  `ω ↦ g_d^{-1}[O, ω)`.
- By Step 2 of `a2-group-embeds-in-rs-two-graph-geometric-proof`, whose proof does not use
  freeness, `γ ∈ Γ` maps each `Ω(p)` (`p` based at `O` of shape `m`) onto some `Ω(p')`.
  There, `[O,γω)(l+n) = γ[O,ω)(l)` for large `l`, with `n = m'' − m`.
- In coordinates this is the arrow `(S', n, g_{d'}^{-1}γg_d, S)`. So `γ` is a compact open
  global bisection of the amplified groupoid `𝒢_Γ^D` on `⊔_{d∈D} 𝒮_{a(d)}`, which is
  `𝒢_Γ ⊗ R_D` restricted.
- **Faithfulness.** Suppose `γ` acts trivially on `Ω`.
  - Then `γ` preserves every apartment, and acts on each by an isometry fixing its
    boundary, that is, a translation.
  - Half-apartment intersections in the three wall directions (thickness) force the
    translation to be `0`.
  - So `γ` fixes every apartment pointwise, and `γ = 1`.
- **Conclusion.** `Γ ↪ F(𝒢_Γ^D)`. By Step 5, `𝒢_Γ` is purely infinite and minimal, so the
  compression of (R1) gives `F(𝒢_Γ^D) ↪ F(𝒢_Γ)`.

## Step 4. Transition counts: irreducible, primitive iff type-transitive

Put `M_j(b,a) = #{j`-successors of `i_a` in class `b}`.
- **Complete reducibility.**
  - Row sums are `q²`.
  - With weights `w_a = 1/|K_a|`, orbit–stabilizer counting over the `Γ`-orbits of pairs
    `(t, t')` of a tile and a successor gives `wM_j = q² w`.
  - A nonnegative matrix with positive left and right eigenvectors for its Perron value is
    completely reducible (no transient classes).
- **Irreducibility and period.** Now the tile-level argument of
  `a2-rs-matrices-irreducible-and-primitive-iff-type-transitive`, Steps 1–6, runs verbatim.
  It uses moves (m1)–(m2), pencils in the links and two-type connectivity, and never uses
  freeness.
  - Hence each `M_j` is irreducible.
  - `M_j` is primitive iff the type-rotation character `θ` is nonzero, and has period 3
    otherwise.

## Step 5. The host (as in the reference proofs)

1. **Rescaling.** Rescale by `n` (`n = 3m` if `θ = 0`) so that every object has at least two
   loops of each colour. When `θ = 0`, restrict to phase 0 and use the skew product over
   `L/nZ²`, as in `type-preserving-vertex-free-a2-groups-embed-in-fp-simple-groups`. Both
   steps need only paths (morphisms) of every large degree in the allowed coset between any
   two objects, which Step 4 gives.
2. **Product with the full 2-shift.** Form `ℭ' = ℭ_Γ^(n) × B_2`, with `N³`-valued degree.
   Arrows of the product split coordinatewise, so its groupoid is `𝒢_Γ^(n) × G_2`.
3. **F_∞ (Li).** Apply X. Li, arXiv:2110.04505, Theorem `thm:deg` (read at source), with
   `P = N³`, `S_P` the nonzero `{0,1}`-vectors, `X = ∂Ω` and `Y` the phase-0 (or all) object
   cylinders.
   - Finitely many objects and local finiteness: Step 1.
   - Condition (F): right cancellation (Li: "(F) holds if ℭ is right cancellative").
   - Condition (t < d): the lemma after `thm:deg`, from at least two loops for every
     `s ∈ S_P`.
   - `ℭ'^*(v,v) = K_a` is finite, hence of type `F_∞`.
   So `F` of the reduction is of type `F_∞`.
4. **Purely infinite and minimal.** As in Step 6 of the reference proof, with morphisms in
   place of paths, using strong connectivity (Step 4).
5. **Essentially principal: aperiodic sectors are dense.** Call `S` aperiodic when no
   `(g,n) ≠ (1,0)` has `gS(l) = S(l+n)` for all large `l`. The isotropy at `S` is trivial
   iff `S` is aperiodic. Put `F_{g,n,L} = {S : gS(l) = S(l+n), l ≥ L}`. It is closed, and it
   contains no cylinder `Cyl(P)`:
   - **n = 0.** Then `g` fixes pointwise every tail beyond `L` of every sector through `P`.
     That union contains balls of radius `R_0`, by RS Lemma `c3`: every vertex within `r` of
     a deep point `z` lies on a sector through `P`. So `g = 1`.
   - **n_1 ≥ 1.** Take `S, S' ∈ Cyl(P)` that agree on the box `[0,M']` but differ at
     `(M'_1+1, 0)`.
     - Such a pair exists: one-column extensions of a parallelogram are in bijection with
       the successor tiles at the bottom, since each column is built by unique joins.
     - Agreement sets are downward closed, so `S` and `S'` agree only where `l_1 ≤ M'_1`.
     - But the relation sends the agreeing position `(M'_1, M'_2)` to the disagreeing
       position `(M'_1, M'_2) + n`. Contradiction.
   - **n_1 ≤ −1.** Pass to `(g^{-1}, −n)`.
   - **n_1 = 0.** Use a pair that differs at `(0, M'_2+1)` instead.

   By Baire, aperiodic sectors are dense, so `𝒢_Γ` is topologically principal, hence
   essentially principal (Hausdorff, Lemma 2.2). The product with `G_2` inherits this.
6. **Homology, perfectness, simplicity.** `H_*` vanishes by Künneth with `H_*(G_2) = 0`
   (`matui-groupoid-homology-kunneth-and-full-shift-vanishing`). Then Li's exact sequence
   (`li-ah-exact-sequence-for-minimal-comparison-groupoids`) makes the full group perfect,
   and Matui (`matui-purely-infinite-minimal-full-groups-have-simple-d`) makes it simple.

**Composition.** Chaining `Γ ↪ F(𝒢_Γ^D) ↪ F(𝒢_Γ) ↪ F(host)` (Steps 3 and
5.1–5.2), and then (R1) for non-type-rotating `Γ`, gives the claim. ∎

## Remark

The free case is the special case in which all `K_a` are trivial and `𝒢_Γ` is the
Kumjian–Pask groupoid. Step 5.5 then reproves aperiodicity without (H3).
