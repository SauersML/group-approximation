---
rg: 2
id: keyed-slots-bypass-the-phase-field-on-boundary-geometry
kind: claim
title: Keyed diversification slots supply the forced plane-varying data, so the phase-field condition (PF) is not needed; the natural tree cocycle is recorded as a test, and minimal lifts over boundary planes are automatically topologically free, with full freeness the one extra gate
requires:
  - boundary-geometry-needs-a-measure-only-on-its-own-factor
  - keyed-diversification-slots-give-plane-constant-minimal-lifts
distinct_from:
  boundary-geometry-needs-a-measure-only-on-its-own-factor: that proves the floating data must be plane-varying and proposes a phase cocycle (PF) to supply it; this shows keyed slots supply it without any phase coupling, retracts (PF) as a requirement, and records the tree-cocycle test.
  keyed-diversification-slots-give-plane-constant-minimal-lifts: that lifts free inputs over Λ_0 x Z^2 with an amenable hierarchy; this records what the same mechanism needs over boundary planes W_3 x W_3, whose hierarchy directions are non-amenable.
  free-effective-minimal-subshifts-lift-to-minimal-sfts-times-z2: that is the Z^2 existence statement, which settles gate E1 given (M2); this does not reprove E1. It records the non-amenable-plane variant and its extra freeness gate.
---

**Status.** Part 1 is a correction. Parts 2 and 3 are ESTABLISHED (lane proofs, elementary,
unreviewed). Part 4 is OPEN.

## Part 1. Correction: (PF) is bypassed

`boundary-geometry-needs-a-measure-only-on-its-own-factor`, Part 3, said that what remains of
gate E1 "has a single shape", a phase field coupled by a `y`-dependent cocycle. That is
superseded.
- **Proposition 3 there stands.** Every solution must carry plane-varying data that is not
  determined by `Λ`-invariant data and the input.
- **Keyed slots supply that data.** The mechanism is that of
  `keyed-diversification-slots-give-plane-constant-minimal-lifts` (695a89096):
  - Durand–Romashchenko floating *identities* at infinite father chains are chosen per plane.
    Each lies in `Adm_π(τ)` for that plane's own table `τ`.
  - Their tuples recur because slots keyed by the table display every admissible tuple. The
    keys are pairwise distinct on every finite window of planes, since the input is free.
- **So no phase coupling is needed.** The hierarchy can stay `Λ`-constant, and plane-constant
  inputs need no measure (Proposition 1 of that node). With the Z^2 lift, gate E1 is (M2) on
  an overgroup, in line with `minimal-free-sft-overgroups-exist-iff-m2-overgroups-exist`.

## Part 2. Test of the natural tree cocycle (recorded; no longer load-bearing)

Take `Λ = Λ_1 * ⟨b⟩` and the tree-glued input `Y_1` of
`free-products-with-z-inherit-m2-from-decidable-free-subshifts`. Its points carry pointer data
toward an end and heights labelled by a Sturmian word of irrational slope `α`.

**The candidate.** The Busemann cocycle `c(λ, y)`: the height of the edge `λ^{-1}·1` minus the
height of the edge `1`, both read in `y`.
- **It is a cocycle.** It is a difference of values of one height function.
- **It is continuous.** On end-type points it depends on the pointer data along a bounded
  path.
- **It is genuinely `y`-dependent.** On any generator it takes values in `{−1,0,1}`,
  according to whether the base edge or its translate is the parent edge of the common star.

**Established fact: labels alone cannot trivialize it.** Let `π : Y_1 -> S_α` read the
Sturmian label sequence along heights at the base. There is no continuous `v : S_α -> Z/2^k`
(`k ≥ 1`) with `v(σ^{c(λ,y)} π y) − v(π y) ≡ c(λ,y)` for all `λ` and `y`.
- Such a `v` would satisfy `v∘σ − v ≡ 1` on the dense set of values `π y` at which some `λ`
  has `c(λ,y) = 1`, and hence everywhere.
- Then `e^{2πi v/2^k}` would be a continuous eigenfunction of the Sturmian shift with
  eigenvalue `e^{2πi/2^k}`.
- But the continuous eigenvalues of a Sturmian shift of irrational slope are
  `{e^{2πi nα}}` (recalled). So this is impossible.

**Not established.** The full criterion (PF1) for `c` asks that no continuous coboundary
exists on all of `Y_1`, not only through the label factor. Fibres, library points and the
ruler schedule could in principle supply one. This is left open, since (PF) is no longer
needed.

## Part 3. Topological freeness is automatic over boundary planes

**Lemma.** Let `Γ = Λ x W_3 x W_3`, let `Z` be a minimal `Γ`-subshift, and suppose `Z` has:
- a factor `Z -> G = B ⊠ B` onto the boundary geometry;
- a factor `Z -> Y_1` onto a free `Λ`-subshift that is invariant under `W_3^2`.

Then the points of `Z` with trivial stabilizer form a dense `G_δ`. So `Z` is topologically
free.

*Proof.*
1. **Stabilizers are small.** A stabilizer of `z` fixes both images, so it lies in
   `Stab(y_1) x Stab(ξ_1) x Stab(ξ_2) = 1 x C_1 x C_2`. Each `C_i` is trivial or infinite
   cyclic (Proposition 2(c) of `strongly-proximal-geometries-are-disjoint-from-measured-inputs`).
2. **A trivial stabilizer occurs.** The ends with trivial stabilizer are those not fixed by any
   hyperbolic element. Only countably many ends are fixed by some element, so trivial
   stabilizers occur. Any `z` over such a pair `(ξ_1, ξ_2)` has trivial stabilizer.
3. **The set is `G_δ`.** It is `∩_{g ≠ 1} {z : gz ≠ z}`, a countable intersection of open
   sets.
4. **It is dense.** It is nonempty and invariant, and in a minimal system the closure of a
   nonempty invariant set is everything. ∎

## Part 4. The non-amenable-plane variant (OPEN)

**Target.** For free effective minimal `Y_1` on `Λ`, a minimal *free* SFT on `Λ x W_3 x W_3`
lifting `Y_1` `W_3^2`-invariantly. It would use:
- the BSS grids of `B ⊠ B` as planes;
- Durand–Romashchenko hierarchies on grids, aligned at the corners of anchored grids;
- tables and keyed slots as in 695a89096.

**Why it matters.** SYNTHESIS v4 retired `Z^2` as a Track A base. Here every hierarchy
direction is non-amenable (Stein–Farley cocompactness, separation, exactness).

**What transfers.**
- The walls play the role of DR's infinite faults.
- The keys are plane tables, so they remain distinct by freeness of `Y_1`.
- Geometry and input sit in commuting factors, so their joining is the product.

**What does not transfer: freeness along `W_3^2`.**
- A hyperbolic `h` fixing `ξ_i` maps anchored grids to anchored grids, corners included.
- So corner-aligned hierarchies and plane-constant tables are `h`-invariant.
- Only floating identities could break the symmetry, and nothing forces them to.
- Part 3 gives topological freeness only.

**Two repairs, both open.**
- (i) Add a `Λ`-constant, `W_3^2`-varying free input, such as a regular Toeplitz subshift or
  the odometer `Ô`. Its data is not plane-constant, so it rides the grids as sequences and
  floats on walls.
- (ii) Show that the route downstream of E1 needs only topological freeness (lane
  bh-g3-topfree).

## Lesson for general BH

The forced floating datum is *data*, not *geometry*.
- Keyed slots let each plane choose its own floating identities, indexed by its own table.
- Freeness of the input makes those indices distinct, and that alone diversifies every
  finite tuple.

So neither phase fields, nor measures, nor boundary geometry are needed for existence (E1).
Boundary geometry becomes relevant only if later gates need non-amenable hierarchy
directions. The price is then freeness along the boundary factor: topological freeness is
automatic there, and full freeness is the one extra gate.

## Referee (bh-ref-e1-b, 2026-09-18): PASS for Parts 1–3; Part 4 correctly marked OPEN

- **Part 1 (correction).** Correct *given* `keyed-diversification-slots-give-plane-constant-minimal-lifts`,
  which passes at design level with one repairable gap: the slot key must be the full level-`K`
  input field, see its Referee section. With that repair the floating identities are still chosen
  per plane and indexed by distinct keys, so the retraction of (PF) as a requirement stands.
- **Part 2 (tree cocycle, not load-bearing).** The eigenvalue argument is correct.
  - `v∘σ − v ≡ 1` would make `e^{2πiv/2^k}` a continuous eigenfunction with eigenvalue
    `e^{2πi/2^k}`.
  - For irrational `α`, `1/2^k ∉ Zα + Z`, so that eigenvalue does not lie in `{e^{2πinα}}`.
  - The density step also needs points with `c = −1`. Those are handled by the cocycle identity
    `c(λ^{-1}, λy) = −c(λ, y)`.
- **Part 3 (topological freeness).** Checked line by line: correct.
  - End stabilizers in `W_3` are trivial or infinite cyclic. Vertex stabilizers of the Cayley tree
    are trivial, so an involution, which inverts an edge, fixes no end.
  - Countability of `Γ` gives both the `G_δ` and the existence of generic ends.
  - Density follows from minimality.
- **Part 4.** OPEN, correctly. Its repair (ii) is already supplied by bh-g3-topfree (2914b739e):
  topological freeness suffices downstream.
