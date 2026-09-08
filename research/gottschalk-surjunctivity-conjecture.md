---
rg: 2
id: gottschalk-surjunctivity-conjecture
kind: claim
title: Every group is surjunctive on every finite-alphabet full shift
root: true
goal: true
refuted_by:
  - leavitt-unit-group-nonsurjunctive
distinct_from:
  gottschalk-surjunctivity-fixed-two-generator-tester: that establishes a reduction to one group; this is the universal conjecture itself, still unresolved here.
  leavitt-unit-group-nonsurjunctive: that seeks one counterexample and would refute this universal positive goal; it is not a positive proof prerequisite.
artifacts:
  - notes/GOTTSCHALK_RESEARCH_2026-09-07.md
  - research/artifacts/gottschalk-information-transport-pinning-control-2026-09-08.md
  - research/artifacts/gottschalk-row-column-deficit-measure-control-2026-09-08.md
  - research/artifacts/gottschalk-injective-image-uniform-gibbs-bridge-2026-09-08.md
  - research/artifacts/gottschalk-quadratic-block-elimination-2026-09-08.md
  - research/artifacts/gottschalk-virtually-abelian-guard-stratification-2026-09-08.md
  - research/artifacts/gottschalk-polycyclic-guard-rank-extension-2026-09-08.md
  - research/artifacts/gottschalk-surjunctive-guard-finite-intersection-proof-2026-09-08.md
  - research/artifacts/gottschalk-off-guard-quadratic-elimination-2026-09-08.md
---

For every group G and every finite nonempty alphabet A, every injective
cellular automaton tau:A^G -> A^G is surjective. An empty alphabet gives
the trivial empty configuration space and causes no additional case.

A cellular automaton means a continuous equivariant self-map of the full
shift, equivalently a map given by a finite memory set and a local rule.
The topology is the product of the discrete alphabet topologies. A proper
invariant subshift cannot replace the full shift in this statement.

This records the positive goal requested on 2026-09-07. Neither the
repository's nonsofic-group constructions nor a completed dependency
reduction settles it. Its negative Leavitt lane remains separate; a
counterexample there would refute this claim.

## Attempts

The finite-observable approach now yields the quantitative criterion
split-ca-defects-force-linear-observable-rank: a strict encoder has a
positive defect seed generating a tower of dimension n delta. It does
not furnish an upper bound contradicting that growth.
reversible-xor-has-linear-observable-rank disproves the proposed universal
sublinear bound, even for the unique decoder of a bijective automaton.
Another invariant must distinguish defect growth from reversible growth.

The fixed-test-group route below uses the existing reduction honestly:
surjunctivity of the test group itself remains an open prerequisite.

The second attack proves split-decoders-have-generic-cantor-fibers. A
strict encoder forces every local decoder to erase a finite perturbation
and have a Cantor subset in every transitive output fiber. The new route
therefore asks for a decoder with just one countable transitive fiber.
No such universal countability result has been proved. In particular,
large topological fibers do not force positive conditional entropy for
the measure supported on the chosen section; the artifact gives a
rectangular counterexample to that inference.

The quantum extension attack now has exact obstruction bounds in
split-ca-quantization-has-sharp-defect. Compression by the encoder's
isometry is local and unital completely positive, but a strict encoder
would give it a norm-one multiplicative defect and put its range
projection at distance 1/2 from the quasilocal algebra. The universal
extension to a unital homomorphism on full matrix observables remains
an open prerequisite. Locality alone does not supply multiplicativity.

The information-transport attack's proposed exact row identity is false,
even for a reversible two-track involution. A degree-64 tree parity shear
with fully iid source and output pins has a discontinuous conditional
entropy for an interval of source-pin densities; finite-exhaustion reveal
accounting misses a uniformly positive atomic contribution. The artifact
gives the exact posterior reduction and proof. This rules out eliminating
all singular information mass as the universal positive argument. A
comparison of the missing row and column contributions remains open and
does not establish surjunctivity here.

The singular row and column deficit measures also have no universal
local ordering: the reversible control gives opposite strict signs on
transposed rectangles in the two pin densities. Their total difference
is exactly the still-unproved percolative-entropy lower bound. The new
control excludes assigning each local deficit a favorable sign; it does
not refute a possible global comparison using cancellation or transport.

The Gibbs bridge proves that the image of an injective CA carries a
unique uniform Gibbs measure, finite dependence, and exact completion
counts `N_Y(E,c)=|A|^|I_E| b_E(c)`. The residual integer counts input
boundary assignments. An overlapping-pair encoding gives a proper
image with all these properties when the output alphabet is larger.
At equal alphabet, no argument removes the boundary loss or licenses
replacement by a forbidden output pattern. This bridge therefore
leaves the headline surjunctivity question open.

The quadratic-feedback attack proves positive exclusions for arbitrary
bipartite operand graphs, target-multiplicative systems without same-track
quadratic terms, and nearest-two cyclic feedback of every length. A
generalized two-block lemma supplies the common argument. The artifact
also excludes every scalar two-term selector by explicit collision or
reduction to a finite memory subgroup, and gives mixed-triangle controls, including
a track-shift conjugate with distinct spatial pairs that resists the
specified initial elimination moves. The unrestricted conjecture remains
open; escaping those moves is not an injectivity or strictness proof.

The support-preservation argument now covers every surjunctive guard
subgroup: injectivity forces surjectivity when configurations supported
in unions of its cosets stay in those unions. Only finitely many
intersections of the original mask stabilizers can arise. A finite
poset of their commensurability classes replaces the earlier rank
induction, and Neumann's finite-coset avoidance theorem removes the
amenability restriction in isolation. Uniform local recoverability is
preserved throughout cancellation. It is enough that the subgroup
generated by the guard's finite memory addresses be surjunctive.
This includes free guards as well as the preceding abelian and
polycyclic cases. The unrestricted ambient group is not proved
surjunctive; the general conjecture remains open.
The conditional theorem and its proof route are recorded as
`surjunctive-guard-subgroups-force-surjectivity` and
`finite-coset-intersection-elimination-proves-guard-transfer`.

A separate elimination theorem needs no surjunctivity assumption on
the guard when exactly one operand of each quadratic monomial lies
in it. Finite unions of guard cosets become recipient color blocks
in a compact invariant coefficient space. The block argument keeps
the coloring fixed and proves uniform locality of each inverse.
For `x+x_r x_(rt)+x_s x_(st)`, a strict candidate must consequently
have every one-from-each-pair guard generate the whole memory group.
Satisfying that condition is not an injectivity proof.
