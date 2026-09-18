---
rg: 2
id: euclidean-building-lattices-lie-in-permutational-bh-class
kind: claim
title: Every discrete cocompact group of automorphisms of a locally finite thick irreducible Euclidean building of dimension at least 2, of any type, lies in the permutational Boone–Higman class B_A, via a finite-type boundary coding whose transfer is automatically completely reducible
distinct_from:
  a2-lattices-embed-in-fp-simple-groups: that is type Ã₂, and uses link arguments for irreducibility and primitivity; this is every type in every dimension at least 2, and shows those arguments are unnecessary. Complete reducibility (a counting identity) plus topological freeness (Ciobotaru–Le Bars) suffice.
  a2-lattices-satisfy-permutational-boone-higman: that is the Ã₂ case of this statement (bh-lattices); this is the general-type theorem, which covers exotic C̃₂ and G̃₂ lattices.
  exotic-a2-lattices-satisfy-boone-higman: that is one special case; this also covers C̃₂ and G̃₂.
artifacts:
  - research/artifacts/gq-bh-bh-groupoid-frontier.md
---

**ESTABLISHED** (lane proof, bh-groupoid 2026-09-18, below. It was checked adversarially by
bh-verify-euclid, PASS conditional on the Ciobotaru–Le Bars trust caveat below. No priority claimed.) It rests on:
- standard building theory (Abramenko–Brown, *Buildings*, Ch. 11; not re-read);
- X. Li's `thm:deg` (arXiv:2110.04505, read at source);
- bh-lattices' `degree-category-full-groups-stabilized-have-type-a-actions` (lane proof);
- Ciobotaru–Le Bars, arXiv:2601.13092, read at source: Proposition `prop minimal` and
  Theorem `thm G-boundary intro`. For a discrete group acting cocompactly on an irreducible
  locally finite affine building, the action on the chambers at infinity is minimal and
  topologically free.
  - **Trust caveat.** This is an unrefereed preprint.
  - Its TeX keeps author notes, all inside `comment` blocks.
  - The live chain behind topological freeness runs from `def generic` (l.777) through the
    barycenter proposition to `prop top free` (l.1567). It was checked for live flags but
    was not re-derived (bh-verify-euclid, trust note T1).

**Verification.** bh-verify-euclid (84896de5e, `research/artifacts/gq-bh-verify-euclid-report.md`)
gives PASS with two wording nits and one trust note.
- The two nits (N1, N2) are applied below, by bh-integrate for the owner.
- The trust note is the caveat above.

## Statement

Let `X` be a locally finite thick irreducible Euclidean building of rank `r` and of dimension
at least 2, and `Γ ≤ Aut(X)` discrete and cocompact. Then `Γ ∈ B_A`. In particular, every group commensurable with a finite
product of such lattices embeds in a finitely presented simple group
(`boone-higman-type-a-class-closed-under-finite-extensions`).

*Scope (bh-verify-euclid N2).* Dimension 1 (trees) is excluded: there the counts are not
phase-only when valences vary. Tree lattices are virtually free and lie in `B_A` by other nodes.

**New cases.** Exotic C̃₂ and G̃₂ lattices, including:
- Kantor's and Essert's panel-regular lattices;
- the chamber-regular C̃₂ lattices of arXiv:2511.08312;
- the non-residually-finite Kazhdan C̃₂ lattices of Titz Mite–Witzel.

For rank `≥ 3` the buildings are Bruhat–Tits and the lattices are linear, so these cases give
nothing new, but the proof is uniform in rank.

## Proof

**Step 0. Box calculus (every type).** Fix a special vertex type, with model sector
`𝔰 = {α_i ≥ 0}` and fundamental coweights `ϖ_i`.
- **Tiles.** The model tile is `𝔱 = {0 ≤ α_i ≤ 1}`. Its faces lie on walls, since
  `α_i(ϖ_j) = δ_ij`, so it is a union of chambers.
- **Boxes.** The boxes `𝔭_m = ⊕_i [0, m_i+1]ϖ_i` tile `𝔰 ≅ N^r × 𝔱`.
- **Embeddings.** Tiles, boxes and sectors are the type-compatible isometric embeddings of
  these models. The type patterns used are those occurring in sectors based at vertices of
  the base type, closed under `Γ`.
- **Composition lemma.** Let `p` be a box of shape `m` and `q` a box of shape `m'` with
  `t(p) = o(q)`. Then `p ∪ q` lies in an apartment, and in a unique box of shape `m + m'`.
  - Take the two-leg curve: along the diagonal of `p`, then from the far corner of `p` to
    that of `q`, with directions perturbed into the open dominant cone.
  - Every positive root strictly increases along it, since `β(Σ c_iϖ_i) > 0` for
    `c_i > 0`. So the chambers it crosses form a gallery crossing each wall at most once.
  - That gallery is minimal in the model. Consecutive chambers lie in `p` or in `q`, so its
    image has the same reduced type, and it lies in an apartment `Σ`.
  - The gallery passes through the extreme chambers of `p` and the far chamber of `q`, and
    the initial chamber of `q` lies in `t(p) ⊆ p`.
  - Boxes are convex hulls of their extreme chambers. So `p, q ⊆ Σ`, and the box is the
    convex hull of the first and last chambers.
- **Finite alignment.** Distinct minimal common extensions of two boxes from one tile have
  disjoint ideals, since a common extension would contain both as initial boxes of the same
  shape. So minimal common multiples are disjoint and finite, and no link girth is needed.

**Step 1. Orbit category.** Define `ℭ_Γ` exactly as in Step 1 of
`a2-lattices-embed-in-fp-simple-groups`: objects are tile classes, morphisms are `(p,γ)`, and
composition uses the composition lemma. It is cancellative and finitely aligned, satisfies
(UFP\*), is locally finite, and has finite unit groups `K_a` (tile stabilizers). Its Li
groupoid is `𝒢_Γ`, the `Γ`-twisted tail equivalence on sectors (Lemma 2.1 there, verbatim).

**Step 2. Γ acts by cylinder exchanges (type-free).**
- For `γ ∈ Γ` and a chamber `ω` at infinity, the sectors `[O,γω)` and `γ[O,ω)` are parallel,
  so they share a subsector.
- So `[O,γω)(l+n) = γ[O,ω)(l)` for some `(l, n)`. By uniqueness of the sector from a tile
  toward `ω`, this then holds at all larger positions.
- The sets `U_{l,n} = {ω : [O,γω)(l+n) = γ[O,ω)(l)}` are clopen, since they read finitely
  many tiles, and they cover the boundary.
- By compactness, `γ` is a finite union of basic bisections of the amplified `𝒢_Γ^D`.
- Faithfulness uses thickness, as in Step 3 of the Ã₂ node. So `Γ ↪ F(𝒢_Γ^D)`.

This replaces the Robertson–Steger sector lemmas `c1`–`c3` and `9B`.

**Step 3. Complete reducibility is automatic.** Let `M_j(b,a)` count the `j`-successors of
`i_a` in class `b`.
- **Counts.** A `j`-successor of a tile `t` corresponds to a chamber `F` at a fixed Weyl
  distance from the far chamber of `t`, with lengths adding. A `j`-predecessor corresponds
  likewise to a chamber at a fixed distance from the initial chamber. By regularity both
  counts depend only on the type pattern ("phase") of `t`: `succ = c_φ` and `pred = c'_φ`.
  The colour-`j` step permutes phases cyclically.
- **The two eigenvectors.** Orbit–stabilizer with `w_a = 1/|K_a|` gives
  `Σ_a w_a M_j(b,a) = w_b·pred(b)`. Summing over phases, `c_φ W_φ = c'_{φ+1} W_{φ+1}`, where
  `W_φ` is the total weight of phase `φ`. So `Π c_φ = Π c'_φ` around each phase cycle.
  Hence phase-constant rescalings of `1` and of `w` are positive right and left eigenvectors
  of `M_j` with the same eigenvalue `ρ`. In constant thickness (for example Ã₂) they are
  simply `1` and `w`.
- **Conclusion.** A nonnegative matrix with positive left and right Perron vectors has no
  transient classes. So every class lies on `j`-cycles for each `j`. Applying this argument
  to `Σ_j M_j` directly is not valid, because the phase rescalings of the Perron vectors can
  differ between colours. Instead, each `M_j` is completely reducible, so every
  single-colour step can be reversed inside its colour class. By (UFP*) every morphism
  factors into such steps. So reachability is symmetric, and `ℭ_Γ` splits into strongly
  connected pieces with no morphisms between pieces. *(Wording corrected per
  bh-verify-euclid N1.)*

**Step 4. Rescaling and embedding.** Choose `n` so that every object has at least two loops
of each colour in `ℭ_Γ^(n)`, which is possible by Step 3. Let `𝒫` be the union of the finitely many pieces that contain decorations,
treated piece by piece (`D` below is the product over pieces). Every `Γ`-arrow stays in one
piece, because tails lie in the component of the first tile.
- Choose a potential `φ: 𝒫^0 → Z^r/L`, where `L` is the lattice generated by cycle degrees,
  with `φ(a) − φ(b) ≡ d(μ)` for every morphism `μ: b → a`.
- The cocycle `lag − (φ(target) − φ(source))` takes values in `L`.
- Skew product over `L/nZ^r`. Then compress into `X_𝒫 × {0}` with morphisms of prescribed
  degree. Every large degree in the right coset occurs: the image of the cycle semigroup in
  the finite group `L/(⊕k_jZε_j)` is a group.
- This gives `F(𝒢_Γ^D|_𝒫) ↪ F(𝒢_Γ^(n)|_{X_𝒫})`. It is the construction of
  `type-preserving-vertex-free-a2-groups-embed-in-fp-simple-groups`, with `L` general.

**Step 5. Effectiveness.** Suppose an isotropy bisection `(g, n)` holds on a cylinder.
- Then `g` fixes every chamber at infinity of that cylinder, an open set.
- By Ciobotaru–Le Bars topological freeness, `g = 1`, and then `n = 0` because sectors are
  injective.
- So `𝒢_Γ` is effective, `F(𝒢_Γ)` acts faithfully, and so does its `O_2`-stabilization.

**Step 6. Type (A).** Form `ℭ'' = ℭ_Γ^(n)|_𝒫 × O_2`.
- Its full group `D` is finitely presented (in fact `F_∞`) by Li's `thm:deg`. The inputs
  are: `P = N^{r+1}`, condition (F) from right cancellation, (t < d) from the loops, and
  finite units.
- By `degree-category-full-groups-stabilized-have-type-a-actions`, `D` acts on clopen sets
  with type (A).
- Steps 2 and 4 put `Γ` inside `D`. ∎

## Lesson for general BH

**Mechanism: finite-type boundary coding.**
- A group acting properly, cocompactly and faithfully on a space with a regular box calculus
  has a boundary groupoid equal to Li's groupoid of a finite degree category with finite
  units.
- The transfer operators are then automatically completely reducible. This is a counting
  identity (`wM = ρw`, `M1 = ρ1`), not a dynamical input.
- So the only dynamics needed is topological freeness.

**Consequence for the Ã₂ work.** The per-type irreducibility and primitivity link arguments,
and the phase bookkeeping of the Ã₂ nodes, are not needed for `B_A`.

**Criterion.** A group that acts faithfully and topologically freely, by twisted tail
equivalence, on the boundary of a finitely aligned right-cancellative degree category with
finite units and regular counts, lies in `B_A`.

**Limit.** Such finite-type hosts have exponentially bounded word problem
(`finite-k-graph-full-groups-have-exponential-word-problem` extends, since the units are
finite). So universality needs codings that grow with the input.
