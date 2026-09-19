---
rg: 2
id: near-representation-amenability-dichotomy
kind: claim
title: A near-representation analogue of the Bekka–Valette dichotomy
root: true
invalidates: [amenable-charge-route]
distinct_from:
  amenable-rep-of-kazhdan-has-fd-subrep: that is the genuine-representation statement, proved; this asks whether the same conclusion survives replacing homomorphisms by near representations, and is open
  bekka-valette-amenable-t-dichotomy: that is the published genuine-representation dichotomy recorded by citation; this is the unpublished near-representation question it raises
  wreath-flexible-hs-stability: that asks whether almost-representations of the acting group are close to genuine ones in normalized HS; this asks whether a rigidity CONCLUSION transfers to near representations, which is not the same as the perturbation being small
---

**Open.** Does the Bekka–Valette dichotomy have an analogue for near
representations? Concretely, in the direction that matters: if `G` has property
(T) and `π : G → U(H)` is an *amenable near representation* in the sense of
Kahl–Schneider — multiplicativity holding only `μ`-almost everywhere, to within
every `ε`, for the invariant charge `μ` — must `π` admit some approximate
substitute for a nonzero finite-dimensional subrepresentation?

## Why this is the pivot

`amenable-charge-route` applies Kahl–Schneider's equivalence: `W` is
hyperlinear exactly when it admits an essentially free amenable near
representation. The lane's value rests on that criterion being independent of
the rigidity branch, and the independence rests entirely on this question being
open.

For **genuine** representations the collapse is complete and proved
(`amenable-rep-of-kazhdan-has-fd-subrep`, and published as
`bekka-valette-amenable-t-dichotomy`): a Kazhdan group's amenable
representations all contain finite-dimensional subrepresentations, which is
where `commutant_no_growth` and the `finrank` invariant size bite. If any
near-representation analogue held, the same collapse would reach the charge
lane and it would die with the rest of the flexible side.

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

This is the same operator-norm-versus-trace-scale mismatch recorded above,
localized to the one line where it bites. It is not a gap in the write-up; it
is where the mathematics actually differs.

## The pivot, restated

So the question is not really about amenability. It is:

> Is there a property (T) for charge-almost-everywhere near representations —
> that is, does a Kazhdan group's near representation with almost invariant
> vectors have a genuine (or approximately genuine) invariant vector, when
> multiplicativity is only assumed `μ`-a.e. pointwise?

A positive answer at that level would give the dichotomy and evaporate the
charge lane. A negative answer at a single Kazhdan group would prove the gap
real. This is a question about property (T) itself rather than about `W`, which
is what makes it worth owning: it can be attacked without touching the wreath
candidate, and either answer is a theorem about Kazhdan groups.

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
