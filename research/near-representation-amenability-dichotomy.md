---
rg: 2
id: near-representation-amenability-dichotomy
kind: claim
title: A charge-visible near-representation analogue of the Bekka–Valette dichotomy
root: true
invalidates: [amenable-charge-route]
distinct_from:
  amenable-rep-of-kazhdan-has-fd-subrep: that is the genuine-representation existence statement, proved; this asks for a positive-charge remnant after replacing homomorphisms by near representations, which the bare existence statement cannot supply
  bekka-valette-amenable-t-dichotomy: that is the published genuine-representation dichotomy recorded by citation; this is the stronger charge-visible near-representation question needed by the wreath route
  wreath-flexible-hs-stability: that asks whether almost-representations of the acting group are close to genuine ones in normalized HS; this asks whether a rigidity CONCLUSION transfers to near representations, which is not the same as the perturbation being small
---

**Open, in its corrected charge-visible form.**  Suppose `G` has property
(T) and `pi:G -> U(H)` is an amenable near representation in the sense of
Kahl--Schneider, with invariant charge `mu`.  Must `pi` admit an approximate
finite-dimensional or invariant sector of **positive `mu`-charge**?  Bare
existence of a nonzero finite-dimensional subrepresentation is insufficient:
`kun-thom-compression-survives-amenable-near-model` supplies an essentially
free amenable genuine representation in which every finite-rank projection
has charge zero.

## Why this is the pivot

`amenable-charge-route` applies Kahl–Schneider's equivalence: `W` is
hyperlinear exactly when it admits an essentially free amenable near
representation. The lane's value rests on that criterion being independent of
the rigidity branch, and the independence rests entirely on this question being
open.

For **genuine** representations the existence statement is complete and proved
(`amenable-rep-of-kazhdan-has-fd-subrep`, and published as
`bekka-valette-amenable-t-dichotomy`): a Kazhdan group's amenable
representations all contain finite-dimensional subrepresentations, which is
where `commutant_no_growth` and the `finrank` invariant size can bite in a
normal finite-dimensional model.  But a bare near-representation analogue is
not enough for the Kahl--Schneider lane: it must produce a remnant of
**positive invariant charge**.

`kun-thom-compression-survives-amenable-near-model` proves this correction on
the actual residually finite Kazhdan actor.  Its residual finite regular
representation is genuine, faithful, amenable and essentially free for a
singular invariant charge.  Bekka--Valette finite-dimensional summands are
present, but every finite-rank projection has charge zero.  Moreover the
strict compressed subgroup and its parent have identical fixed spaces, and
their common fixed projection has charge zero.  Consequently even the genuine
dichotomy does not by itself close the charge lane.  The needed open statement
is a **charge-visible** near-representation dichotomy, or an invariant Cartan
completion which makes the lamp sector visible to the charge.

## Two reasons it is not merely a technicality

**The topologies are incompatible, so no repair is available from stability.**
The obvious attempted bridge is to assume `G` flexibly HS-stable, replace the
near representation by a genuine one, and apply the theorem. This fails, and
not for a fixable reason: amenability is the existence of an invariant state on
`B(H)`, states are continuous for the operator norm, and flexible HS-stability
supplies only `‖·‖₂` closeness. Invariance of the state does not survive an
HS-small perturbation. Amenability lives at the operator-norm scale and
near-ness at the trace scale.

**A calibration says the near-ness is load-bearing.** Observed by
`cairn-scout`, and recorded as their inference rather than a theorem. Were
genuine amenable representations enough for the criterion, then for a Kazhdan
group hyperlinearity would reduce to possessing a nonzero finite-dimensional
subrepresentation — making every minimally almost periodic Kazhdan group
non-hyperlinear. Infinite simple Kazhdan groups are minimally almost periodic,
none is known to be non-hyperlinear, and such a conclusion would settle far
more than is settled. So Kahl–Schneider's use of near representations is
forced, not stylistic, and the charge witness evades the rigidity collapse by
construction.

Neither reason is an argument that the analogue is false. They are reasons the
question is not answerable by inspection, which is what makes it worth a node.

## Where the genuine proof breaks, exactly

Owned by `cairn-wreath` per the team lead. The first useful thing is that the
failure localizes to a single step, and naming it converts the question into a
sharper one.

The proof of `amenable-rep-of-kazhdan-has-fd-subrep` has three moves. Move 1 —
invariant state on `B(H)`, then Day's trick and Powers–Størmer, producing unit
vectors `ρ_i^{1/2} ∈ HS(H)` almost invariant for `Ad π` — **never uses
multiplicativity of `π` at all**. It goes through verbatim for a near
representation. Move 3, extracting a finite-rank spectral projection from a
nonzero invariant Hilbert–Schmidt operator, is pure spectral theory and also
survives.

Everything turns on move 2: property (T) applied to `Ad π` on `HS(H)`. Property
(T) is a statement about **genuine** unitary representations — every unitary
representation with almost invariant vectors has a nonzero invariant vector —
and for a near representation `Ad π` is only a near representation of `G` on
`HS(H)`.

**And its defect is measured in the wrong norm.** Writing `u = π(gh)`,
`v = π(g)π(h)`, for `T ∈ HS(H)`

    ‖Ad π(gh)T − Ad π(g)Ad π(h)T‖₂ = ‖uTu* − vTv*‖₂ ≤ 2‖u − v‖_op · ‖T‖₂,

so the multiplicativity defect of `Ad π` on `HS(H)` is controlled by the
**operator-norm** defect of `π`. Kahl–Schneider's notion controls something
else entirely: `‖π(gh)x − π(g)π(h)x‖ ≤ ε` for `μ`-almost every basis vector
`x`. A charge-null set of basis directions can carry an order-one operator-norm
defect — finitely additive charges annihilate sets that are infinite, so
"`μ`-null" is very far from "small". Hence `Ad π` need not be close to any
genuine representation of `G` on `HS(H)` in any sense property (T) can consume,
and move 2 has nothing to stand on.

There is also no hidden rescue by first passing to the state GNS space.
`singular-near-defects-vanish-on-canonical-genuine-sector` proves that the
cyclic subspace generated by `C^*(pi(G))` does carry a genuine representation
(the regular representation in the free-character case), but every
two-sided translate of every multiplicative defect is zero on that subspace.
On the rest of the singular GNS space the defects may survive, but the group
law may fail.  Thus the canonical GNS construction supplies either the
representation or the defect-derived coefficient vectors, never both; a
charge-visible theorem must genuinely propagate multiplicativity beyond the
cyclic trace sector.

This is the same operator-norm-versus-trace-scale mismatch recorded above,
localized to the one line where it bites. It is not a gap in the write-up; it
is where the mathematics actually differs.

## The pivot, restated

So the question is not really about amenability. It is:

> Is there a property (T) for charge-almost-everywhere near representations —
> that is, does a Kazhdan group's near representation with almost invariant
> vectors have a genuine (or approximately genuine) invariant sector of
> **positive `mu`-charge**, when multiplicativity is only assumed `mu`-a.e.
> pointwise?

A positive answer at that level would give the dichotomy needed by the charge
lane.  The residual finite countermodel proves that “nonzero” cannot replace
“positive charge,” even for a genuine representation.  The remaining question
is about property (T) together with the specified charge, rather than ordinary
property (T) alone.

**A construction hazard, for whoever tries the negative direction.** The
tempting witness is a genuine representation perturbed on a charge-null set of
basis directions. That will not refute anything by itself: if the amenability
of the perturbed map is inherited from the genuine part, Bekka–Valette applies
to that part and returns the finite-dimensional structure. A refuting witness
needs the *charge-null junk* to carry the amenability, not merely to exist. I
have not found one and am not claiming it can be done.

## Status

Nothing read on either side bears on it. `cairn-scout` reports finding no
treatment of it in Li–Ng, in Kahl–Schneider, or in the surrounding literature,
and states no evidence in either direction; this node inherits that. It is the
single question whose resolution decides whether `amenable-charge-route` is a
genuinely separate attack on `hyperlinear-wreath-model` or the rigidity fork
wearing different notation.
