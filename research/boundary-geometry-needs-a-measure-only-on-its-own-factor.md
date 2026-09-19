---
rg: 2
id: boundary-geometry-needs-a-measure-only-on-its-own-factor
kind: claim
title: On Λ x W_3 x W_3 the boundary geometry is disjoint from Y_1 ⊠ Ô for every minimal Y_1 and the free profinite odometer Ô of W_3^2, so no invariant measure is needed on the envelope; the floating data must then be a plane-varying phase field, which coboundaries and homomorphisms cannot supply
distinct_from:
  strongly-proximal-geometries-are-disjoint-from-measured-inputs: that proves disjointness for inputs with an invariant measure on the whole group; this shows the measure is needed only on the factor carrying the geometry, where a profinite odometer supplies it, and derives the forced shape of the floating locus.
  decidable-groups-carry-free-subshifts-with-decidable-language: that is premise (D) for the envelope; this shows (D) needs no measure added. The tree-glued inputs built from (D) have no invariant measure, and none is needed.
  plane-coupled-floating-tuples-are-jointly-diversifiable: that is the Z^2 form of the crux; Part 3 here is the boundary-geometry form, stated as a phase-field condition with two named dead classes.
---

**ESTABLISHED: Parts 1 and 2 and the kills in Part 3 (lane proofs, elementary, unreviewed).**
**OPEN: the phase-field statement (PF) at the end.**

Setting.
- `Λ` is finitely generated with solvable word problem. For the master route it is
  `Λ_1 * Z`, as in `minimal-free-sft-via-decidable-free-subshift-of-the-envelope`.
- `Γ = Λ x W_3 x W_3`, with `W_3 = Z/2*Z/2*Z/2`.
- `G = B ⊠ B` is the boundary geometry of `strongly-proximal-geometries-are-disjoint-from-measured-inputs`,
  Part 3. `Λ` acts trivially on it.

## Part 1. The measure is needed only on the geometry factor

**Proposition 1.** Let `Y_1` be any minimal `Λ`-system and `Y_2` any minimal
`W_3^2`-system with an invariant probability measure, and let `Y = Y_1 ⊠ Y_2`, each factor
acting trivially on the other. Every closed `Γ`-invariant `J ⊆ G x Y` with `π_Y(J) = Y` equals
`G x Y`. In particular `G x Y` is minimal.

*Proof.*
- Let `(x, y_1, y_2) ∈ J`. `Λ` fixes `x` and `y_2` and acts minimally on `Y_1`, so
  `{x} x Y_1 x {y_2} ⊆ J`.
- Hence `J = { (x,y_1,y_2) : (x,y_2) ∈ J' }` for the projection `J'` of `J` to `G x Y_2`.
- `J'` is closed and `W_3^2`-invariant, and it maps onto `Y_2`.
- `G` is minimal and strongly proximal as a `W_3^2`-space. So Lemma 1 of the required node
  gives `J' = G x Y_2`. ∎

**Proposition 2 (the measured factor exists and is effective).** `W_3^2` has a free,
minimal, uniquely ergodic, effectively closed action: a profinite odometer `Ô`.

*Proof.*
- **Chain.** Let `N_k` be the intersection of all normal subgroups of `W_3^2` of index at
  most `k`.
  - Each `N_k` has finite index: a finitely generated group has finitely many subgroups of
    each index.
  - The chain is computable uniformly in `k`. The group is finitely presented, so its
    homomorphisms to finite groups of order at most `k` can be listed.
  - `∩ N_k = 1`, because `W_3^2` is residually finite (it is virtually free × virtually free,
    hence linear).
- **The odometer.** `Ô = lim W_3^2/N_k`, with the group acting by left translation, is a
  compact group containing a dense copy of `W_3^2`.
- **Properties.**
  - Minimal: the translation orbit is dense.
  - Uniquely ergodic: Haar measure is the only invariant measure.
  - Free: residual finiteness.
  - Effectively closed: as a subset of `∏_k W_3^2/N_k` with computable compatibility maps
    and computable translations, coded in `{0,1}^N`. ∎

**Consequence.** Take `Y = Y_1 ⊠ Ô`, with `Y_1` from (M2) for `Λ`, e.g. through (D) and
the tree gluing of `free-products-with-z-inherit-m2-from-decidable-free-subshifts`.
- `Y` is effectively closed, minimal and free.
- Every joining of `Y` with the geometry `G` is the product.
- This is the input needed by BSS Question `Q:minimal` for `Γ`. No measure is ever asked
  of `Λ`, so premise (M2μ) is withdrawn.

**Remark (sketch; standard tree dynamics).** The tree-glued (M2) inputs on `Λ_1 * Z` have
no invariant probability measure.
- They factor onto pointer data of end type or sink type.
- The sink vertices form infinite orbits, so they carry no invariant probability measure.
- `Λ_1 * Z` contains two hyperbolic elements with disjoint fixed pairs, such as `ab` and
  `b^{-1}ab·b` for `a ≠ 1`. Their north–south dynamics exclude an invariant measure on the
  ends.
- So an (M2μ) premise on the envelope would have contradicted the (D) route. The measure
  has to live where the geometry lives.

## Part 2. What floats, and where

With `G` as above, every element of `Γ` is the origin of an anchored grid. The unanchored
("wall") grids lie over the countably many ends with an eventually constant colour sequence,
and they sit at the same position in every `Λ`-plane.

**Proposition 3 (the hierarchy must vary along `Λ`).** Let `Z` be a minimal `Γ`-SFT, and
let `φ : Z -> Y_1` be a `W_3^2`-invariant factor onto a non-SFT minimal `Λ`-subshift.
Suppose:
- `τ : Z -> T` is a `Λ`-invariant factor;
- the rest of each point is a continuous function of `τ` and `φ` (call this (Det)).

Then we have a contradiction.

*Proof.* (Det) makes `(τ,φ)` injective. `T x Y_1` is minimal, because its orbits are
products. Theorem 3(iii) of the required node then makes `Y_1` of finite type. ∎

**Instances killed (each satisfies (Det) with a `Λ`-invariant `τ`):**
- **(a) Deterministic computation on geometry-driven hierarchies.** Durand–Romashchenko–Shen
  fixed-point hierarchies are aligned at the corner of every anchored grid, the wall phases
  agree across planes, and the computation is a function of the hierarchy and the letters.
  - `τ = (geometry, hierarchy)` is `Λ`-invariant.
- **(b) Floating data tied to the letter layer.** Any design whose floating data is tied to
  the letter layer by twin checks at every level, including on walls.
  - The data is then determined by `y_1`.

So in every solution some data is plane-varying and not determined by
(`Λ`-invariant data, `y_1`).
- That data must still recur in anchored regions, where (Det) holds.
- So its windows must locally look like data computed from `y_1`. This is the
  joint-diversification crux, in its boundary-geometry form.

## Part 3. The phase-field form of the crux

**Phase fields.** The natural plane-varying datum is a hierarchy phase `ψ(λ)` per plane. It
lives in a 2-adic odometer `Z_2^2` for 2-dimensional hierarchies.
- Local rules can tie adjacent planes only by bounded integer shifts:
  `ψ(λs) = ψ(λ) + c(s, y_1|_{λF})` with `c ∈ Z^2`, `|c| ≤ D`.
- Consistency around the relators of `Λ` makes `c` a continuous cocycle
  `Λ x Y_1 -> Z^2`.

**Dead classes (proved).**
- **(i) Coboundaries.** If `c(s,y) = β(sy) − β(y)` with `β` continuous, then `ψ = β(λ·y_1)`
  plus a `Λ`-invariant constant. So `ψ` is determined by `y_1`, and Proposition 3 applies.
- **(ii) Homomorphisms.** If `c` does not depend on `y`, it is a homomorphism `Λ -> Z^2`.
  - It is trivial on every minimally almost periodic subgroup `K`: composing with an
    injective dense map `Z^2 -> T^2` gives a homomorphism to a compact group, which is
    trivial.
  - So phases are constant along `K`-cosets. This recovers case (iii) of
    `nonamenable-products-have-minimal-sft-extensions-of-free-inputs`.

**What survives (proved).**
- **Supply.** On `Λ = Λ_1 * ⟨b⟩`, cocycles are abundant: set `c(a,·) = 0` on generators of
  `Λ_1` and `c(b,·) = f` for any continuous `f : Y_1 -> Z^2`. The relators of `Λ_1` are then
  satisfied, and `b` occurs in no relator.
- **No m.a.p. kill.** A `y`-dependent cocycle meets no minimally almost periodic
  obstruction. The kill of `simple-subgroups-act-trivially-on-equicontinuous-factors`
  concerns equicontinuous *factors*, and the skew product `Y_1 x_c Z_2^2` is an *extension*
  of `Y_1`.

**(PF), OPEN.** There are a cocycle `c` of this kind and a coupling of the phases in the two
`W_3` directions such that:
- **(PF1)** the skew product `Y_1 x_c Z_2^2` is minimal. By the standard criterion for
  compact abelian group extensions (recalled, not re-proved), this holds iff for every
  nontrivial character `χ` of `Z_2^2`, `χ∘c` is not a continuous coboundary into the circle;
- **(PF2)** every finite window of a wall grid, including the phases and the `Ô`-sequence
  data it carries, occurs in an anchored grid of some plane.

With (PF), Proposition 1 gives joint recurrence of geometry and input, and the
Durand–Romashchenko fixed-point bookkeeping gives recurrence inside grids. (PF) is then what
remains of gate E1 on this route, together with (D) for `Λ_1`. That last step is a sketch;
the full minimality proof is not written.

## Lesson for general BH

The measure that kills synchronization is needed only on the factor that carries the
geometry, and a profinite odometer of the boundary factor supplies it for free. The envelope
needs only (D), which is fortunate, because tree-glued inputs are boundary-like and carry no
invariant measure.

What is left of gate E1 has a single shape: a plane-varying phase field coupled to the input
by a genuinely `y`-dependent integer cocycle.
- Coboundaries die by determination.
- Homomorphisms die on minimally almost periodic inputs.
- The free `Z` factor that (D) already introduces is exactly where such cocycles live,
  since it is unconstrained by relators.

So one extra free factor serves both halves: it glues the input (tree) and it carries the
phase cocycle.
