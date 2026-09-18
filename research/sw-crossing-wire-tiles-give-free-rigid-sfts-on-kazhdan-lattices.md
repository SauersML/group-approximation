---
rg: 2
id: sw-crossing-wire-tiles-give-free-rigid-sfts-on-kazhdan-lattices
kind: claim
title: A crossing-wire fixed-point tile set can be laid out SW-deterministically; its Busemann transplants are free quantum-rigid SFTs over every Kazhdan Ã2 lattice of the transplant Setting, over F_m x F_n and over every BMW group
requires:
  - crossing-wire-fixed-point-tile-sets-are-quantum-rigid
  - a2-busemann-transplants-preserve-quantum-rigidity
  - tree-product-busemann-transplants-preserve-quantum-rigidity
distinct_from:
  crossing-wire-fixed-point-tile-sets-are-quantum-rigid: that builds a free rigid Z^2 SFT with a two-way Turing head; this lays the same mechanism out with information flowing only rightward and upward, so that the tile is determined by its left and bottom neighbours and the shift can be transplanted.
  a2-busemann-transplants-preserve-quantum-rigidity: that reduces free rigid SFTs over Kazhdan Ã2 lattices to a free rigid cone-deterministic Z^2 fibre; this supplies the fibre.
  a2-lattice-boundary-skew-shifts-are-quantum-rigid: that gives rigid SFTs over the same lattices that are only topologically free; these are free.
  four-way-deterministic-sft-rigidity-lives-on-axis-faults: that shows determinism alone cannot certify hierarchical tile sets; here the certificate is co-location, and determinism is used only to make the shift transplantable.
---

**CONDITIONAL** (lane bh-invent-04, 2026-09-18; not reviewed; no priority claimed). It rests on:
- (a) `crossing-wire-fixed-point-tile-sets-are-quantum-rigid`, a lane proof for which referee review is
  recommended;
- (b) the Layout Lemma below, a design sketch in the same style as that node's construction step.
  It was not verified line by line.

## Layout Lemma (SW-deterministic crossing wires)

There is a self-similar Wang tile set `τ` satisfying (L0)–(L3) of
`crossing-wire-fixed-point-tile-sets-are-quantum-rigid`. In each macrotile, conditions (L4′) and (SW)
hold in place of (L4):
- **(L4′)** the computation zone is the space-time diagram of a one-way cellular automaton (information moves
  only rightward, time upward). Row `0` holds input copies, program bits and blanks, and the zone accepts
  exactly when the bottom and left colours are those of a tile of `τ`. It then writes that tile's top and
  right colours on output wires;
- **(SW)** every tile of `τ` is determined by its left and bottom colours.

*Design.*
- Coordinates `(i, j) mod N` are read from the left and bottom edges.
- Bottom-side bits enter going up, and left-side bits enter going right.
- Each input fans out into one row copy and one column copy. Every copy flows right or up and ends before the
  opposite margins. The fan-out, turn, crossing `(a, a, b, b)` and wire-end tiles all have their right and top
  edges fixed by their left and bottom edges.
- Two bottom inputs `x_1 < x_2` cross where the row copy of input 1 meets the column of input 2. Left
  inputs are handled symmetrically, and a bottom input and a left input cross at once. So (L3) holds
  for all pairs of inputs.
- Outputs are functions of the inputs. They leave the zone going up or right toward the top and right
  sides, where the margins carry only that side's bits (L1). Corners are blank.
- One-way cellular automata are computationally universal, since the tape can move right instead of
  the head moving left. So the DRS fixed-point construction (arXiv:0910.2415, §2.3, recalled) closes
  with a zone of size `poly(log N)` inside an `N × N` macrotile, for all large `N`. The simulated tile
  set is then `τ` itself, and it is SW-deterministic by construction.

**The crossing-wire proof applies verbatim.** Its Step 2(c) needs only that every zone edge is reached from
row `0` by the face rule. Here every right and top edge is a function of the left and bottom edges of its
face. The rest of the proof (Steps 1, 2(a), 2(b), 2(d), 3–5) uses (L0)–(L3) and determinism alone. Crossings
among outputs are not needed, because outputs lie in the algebra of the inputs.

## Theorem

Let `Ω_τ` be the tiling shift of a Layout-Lemma tile set.
1. **Over `Z^2`.** `Ω_τ` is free, quantum rigid over every field at every scale `D >= 1`, and
   SW-deterministic.
2. **Cone form.** Take `M : Z^2 -> L` with `M(−e_1), M(−e_2) ∈ C°`. For example, in a sector basis
   `(a, b)`, take `M(−e_1) = 2a + b` and `M(−e_2) = a + b`; this has determinant 1. Then `Ω_τ ∘ M^(−1)`
   is cone-deterministic in the sense of `a2-busemann-transplants-preserve-quantum-rigidity`. With
   coordinates chosen the same way, it is also cone-deterministic in the sense of
   `tree-product-busemann-transplants-preserve-quantum-rigidity`.
3. **Transplants.** The Busemann transplant of `Ω_τ ∘ M^(−1)` is a **free, quantum-rigid SFT** over:
   - every torsion-free, type-preserving Ã2 lattice acting simply transitively on one vertex type (for
     example, the index-3 subgroups of torsion-free CMSZ groups), unconditionally with the skeleton `P` of
     `a2-lattice-boundary-skew-shifts-are-quantum-rigid`. These groups are finitely presented, one-ended and
     Kazhdan;
   - `F_m × F_n` and every BMW group, irreducible ones included.
4. **Crossed products.** For each such group `Γ` and every field `k`, `LC(X, k) ⋊ Γ` is finitely presented
   with `Γ` acting freely (`quantum-rigid-sfts-over-fp-groups-have-fp-crossed-products`). By
   `fp-crossed-products-force-sft-over-any-group`, `X` is necessarily an SFT.

Minimality is not claimed at any stage.

## What this closes and what it leaves

- **It closes the free half of gate G2 over one-ended Kazhdan groups.** This is modulo (a) and (b).
  `a2-lattice-boundary-skew-shifts-are-quantum-rigid` left freeness open there. Freeness now comes from
  the aperiodic fibre, and rigidity from co-location in the fibre and cylinder transport in the
  skeleton.
- **It does not give minimality.** The obstruction is the fibre: `Ω_τ` has faults.
  - A minimal sub-SFT of `Ω_τ`, or a Durand–Romashchenko minimal version with deterministic slots, would
    stay rigid (`quantum-rigidity-passes-to-sub-sfts`).
  - It would stay SW-deterministic if the minimality mechanism flows only rightward and upward. Then the
    transplant's minimality is the next question.
- **Programmability.** The zone is universal, so a decorated version carries computations (as in Item 5
  of `busemann-transplants-give-free-sfts-on-building-lattices`), still free and rigid.

## Lesson for general BH

- **Two independent jobs, two mechanisms.** Co-location certifies rigidity in the fibre, and cylinder
  transport carries it through non-amenable geometry. A single design rule makes both apply: *every pair
  of inputs meets, and information flows into one open half-plane*.
- **One-way flow costs nothing.** One-way universality means the flow restriction does not limit
  computation. So the fixed-point method, the rigidity certificate and the Busemann transplant compose.
- **Consequence.** The first free quantum-rigid SFTs over one-ended Kazhdan groups follow, conditional on
  one reviewed lemma and one careful layout.
- **Next gate.** For the master route, E2 over Kazhdan lattices is now reduced to minimality. That points
  at a Durand–Romashchenko minimal fixed point with one-way flow and complete crossings.
