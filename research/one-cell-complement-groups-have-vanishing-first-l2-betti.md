---
rg: 2
id: one-cell-complement-groups-have-vanishing-first-l2-betti
kind: claim
title: The fundamental group of a one-cell complement of a finite contractible 2-complex has vanishing first L²-Betti number
distinct_from:
  contractible-2-complex-minus-a-cell-is-aspherical: that is asphericity of one-cell complements; this L² vanishing implies it, but an aspherical 2-complex with χ = 0 can still have positive second L²-Betti number, so the converse is not automatic.
  whitehead-one-cell-counterexamples-have-positive-first-l2-betti: that is the established implication from non-asphericity to a positive first L²-Betti number; this is the open vanishing statement for every one-cell complement.
  l2-normal-rank-bound-fails-for-torsion-free-groups: that refutes the torsion-free Osin--Thom bound with countable groups that are not finitely generated; this asks for vanishing only for the finitely presented weight-one groups of one-cell complements, which those counterexamples do not reach.
artifacts:
  - research/artifacts/ideas-topology-2026-09-14.md
---

**OPEN.** For every finite connected contractible 2-complex L and every open 2-cell e of L,
b₁^(2)(π₁(L − e)) = 0.

**Consequences.**
- It implies `contractible-2-complex-minus-a-cell-is-aspherical`, through the route
  `one-cell-l2-vanishing-gives-one-cell-whitehead`.
- It therefore implies `kervaire-killing-form-holds-over-nonnegative-deficiency-groups`,
  through the route `kervaire-killing-form-via-one-cell-whitehead`.
- So it is at least as hard as the balanced killing form of Kervaire--Laudenbach.

**Relation to Osin--Thom.** A one-cell complement group is the normal closure of one
element. For torsion-free one-cell complement groups, this claim is the finitely presented
case of the Osin--Thom inequality β₁^(2) ≤ nrk − 1 (arXiv:1108.2411, Conjecture 1.3, as
quoted in `l2-normal-rank-bound-fails-for-torsion-free-groups`).

**Recalled instances, not pinned in this lane.**
- Knot groups. Wirtinger presentations are LOT presentations, and knot exteriors are
  aspherical 3-manifolds with torus boundary. Their L²-Betti numbers vanish (Lott--Lück).
- Two-generator balanced presentations of the trivial group with one relator removed.
  These give torsion-free one-relator groups on two generators, which have b₁^(2) = 0
  (Dicks--Linnell).

No one-cell complement group with b₁^(2) > 0 is known to this lane, and none was searched for.
