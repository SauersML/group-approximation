# (★′) over a Clapham square: how far the construction goes, and exactly what is missing

Lane bh-star-a, 2026-09-18.
- **Target.** Construct the v5 merged object (★′) over the Track A group `Λ = Λ₁ × Λ₁`, where `Λ₁` is
  a Clapham envelope (finitely presented, decidable, containing `G × F₂`). (★′) means a quantum-rigid,
  minimal, topologically free SFT with torsion-free isotropy.
- **Status.** This is a strategy report. The two claim nodes it cites are elementary lane proofs, not
  reviewed.

## 1. Verdict in one paragraph

**Constructed.** (★′) exists over `Λ₁ × Λ₁` whenever `Λ₁` lies in the class 𝒯, which consists of:
- groups acting cocompactly and strongly faithfully on a locally finite tree, with finitely generated
  vertex stabilizers;
- torsion-free cocompact lattices on products of such trees;
- finite products of these.

The nodes are `locally-finite-tree-end-shifts-are-quantum-rigid-sfts` and
`tree-product-lattices-carry-rigid-topologically-free-sfts`. This gives the first (★′) instances over
groups that are not residually finite (`BS(2,3)`) and over infinite finitely presented simple groups
(Burger–Mozes).

**Where it stops.** A Clapham envelope of a *hard* input (one with a non-residually-finite (FA) subgroup,
e.g. a simple Kazhdan group) is never in 𝒯, and cannot be made to act usefully on any locally finite tree
geometry. What is missing is exactly one of the three statements (M1)–(M3) of §5.

## 2. The square adds nothing to rigidity

- **Products.** If `X₁` is (★′) over `Λ₁`, then `X₁ ⊠ X₁` is (★′) over `Λ₁ × Λ₁`.
  - Rigidity: `quantum-rigidity-is-product-stable`.
  - Minimality and topological freeness: as in `master-route-needs-only-topological-freeness`, item 4.
  - Torsion-free isotropy: a nontrivial `(f₁, f₂)` of finite order fixing `(x, y)` would need
    `f₁ x = x` and `f₂ y = y` with some `f_i ≠ 1` of finite order.
  - So the square is needed only for **existence** (Barbieri–Sablik–Salo self-simulation, gate 4 of v5),
    never for rigidity.
- **Coupled, non-product SFTs over the square.** Suppose the `Λ₂`-side compression has an attractor.
  - Corollary C of `attracting-boundary-factors-fix-commuting-actions` makes the `Λ₁`-side act trivially
    on that factor, so the input acts in the fibres.
  - `path-folded-sfts-are-quantum-rigid-only-if-the-fibre-is` then imports the fibre's rigidity problem
    unchanged.
  - Either way the problem is (★′)-type rigidity over `Λ₁` itself.

## 3. Commuting inputs are forced into isotropy

**Lemma (centralizers fix attractors).** Let `Λ` act on a compact space `X`, and let `(a, c₊)` be an
attractor: the basin `{c : aⁿc → c₊}` contains a dense open set `O`. Then every `g` commuting with `a`
fixes `c₊`.
- *Proof.* `O ∩ g⁻¹O` is open and nonempty, so it contains some `c`. Then `aⁿ(gc) → c₊`, and also
  `aⁿ(gc) = g(aⁿc) → g c₊`. So `g c₊ = c₊`. ∎

**Consequence for Track A.**
- In `G × F₂ ≤ Λ₁`, suppose the compression that makes the SFT rigid comes from attracting elements of
  `F₂`, as in every input-free rigidity mechanism known (end shifts, Ã₂ skew shifts). Then `G` fixes every
  attracting point of those elements. **The input sits in isotropy.**
- **In a tree coding**, if some `h ∈ F₂` is hyperbolic, then `G ≤ C(h)` preserves the axis of `h`. So
  - `G` has a subgroup `G₀` of index at most 2 acting on the axis by translations;
  - the kernel `G₁` of the translation length fixes the axis pointwise, so it lies in a vertex
    stabilizer, which is residually finite by item 4 of the one-tree node;
  - so `G` is virtually (residually finite)-by-cyclic.
- A hard `G` is excluded. This is the precise form, for trees, of v5's "hard inputs sit at an infinite
  emitter".

## 4. Why hard inputs never enter 𝒯

- **Elliptic subgroups.** In a topologically free locally finite tree coding, every vertex stabilizer
  embeds in the profinite group `Aut(T)_v`, so every (FA) subgroup is residually finite. In a
  tree-product lattice, (FA) subgroups fix a vertex of the product and are finite.
- **Kazhdan inputs.** By `kazhdan-simple-groups-act-only-on-exotic-2d-buildings`, a group with (FA) and no
  finite quotients acts trivially on every tree. So it is elliptic, hence trivial in 𝒯.
- **Scaling is not enough.** Tree codings reach non-residually-finite groups only through their scaling
  (hyperbolic) part. This covers `BS(2,3)` and Burger–Mozes, but no input whose hardness lives in an (FA)
  subgroup.
- **Infinite valence.** Letting a vertex have infinite valence (as for `Z/2 ∗ G`) makes the naive coding a
  one-or-less condition over `Stab(v)`, which is not of finite type. That is the stabilizer-engine space of
  `simple-inputs-have-finitely-presented-stabilizer-engines`, v5 gates 1–2.

## 5. Exactly what is missing

Let `G` be a finitely generated decidable group with a non-residually-finite (FA) subgroup. (★′) over some
finitely presented `Λ₀ ⊇ G` (in particular over a Clapham square) needs at least one of the following.
All three are OPEN. (M1) and (M3) are v5 gates; (M2) is the only geometric escape left by the Kazhdan
filter.

- **(M1) Infinite-emitter finite type (v5 gates 1–2).** A finite-type coding of a compression system in
  which `G` fixes a point of infinite local valence. By §3 this is where `G` must sit whenever it commutes
  with a compressing element. By item 4 of the one-tree node, the point cannot be of finite valence.
  First test: finite presentation of Reid's group `[[(Z/2 ∗ Z) ⋉ X]]` (bh-free-56, bh-free-60).
- **(M2) Non-tree compression with a nontrivial `G`-action.** An fp overgroup of `G` acting on a
  compression geometry that is not a locally finite tree and not a Bruhat–Tits building, so that `G` is
  not forced to be elliptic. Exotic Ã₂ buildings are the one known candidate:
  - rigid SFTs exist over their cocompact lattices (`a2-lattice-boundary-skew-shifts-are-quantum-rigid`,
    conditional on its host theorem);
  - the Kazhdan filter of 813bff6dd does not reach them.

  The open question is whether an fp group acting on an exotic Ã₂ building can contain a Kazhdan simple
  group acting without a fixed point.
- **(M3) Programmable determinism (v5 gate 3).** A rigid SFT whose rigidity comes from determinism rather
  than attractors, so that §3 does not apply. Such an SFT can carry the input in its language (Z²
  fault-crossing, DRS fixed-point tiles).

**What is not missing.**
- Rigidity at finite valence: it is automatic, by descent plus monotone chains.
- Coupling of several compression directions: it is automatic under cocompactness.
- Topological freeness: it is exactly strong faithfulness.
- The square: it contributes only existence.

## 6. Design rules extracted

1. **Descend before you chain.** Any coding whose sites overcount a geometric object, e.g. group
   elements over vertices, is rigid as soon as the object's own idempotents are. Consistency rules along
   finitely generated stabilizers force the idempotents to be constant on fibres (Lemma 2 of the route).
2. **Couple, never join.** Independent layers over one group fail rigidity by the wall certificate
   (item 3 of the tree-product node). Layers are rigid together when the stabilizer of one layer's
   geometry acts cocompactly on the other's.
3. **Attractors pin commuting inputs.** Any input commuting with a compressing element lives in isotropy
   (§3). So Track A with `G × F₂` is an isotropy design, whether intended or not. The ring route then needs
   `G` torsion-free (K′ trace detector).

## 7. Nodes

- `locally-finite-tree-end-shifts-are-quantum-rigid-sfts` (claim) with
  `locally-finite-tree-end-shift-rigidity-proof` (route).
- `tree-product-lattices-carry-rigid-topologically-free-sfts` (claim, proof inline).
