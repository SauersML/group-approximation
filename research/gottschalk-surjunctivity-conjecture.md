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
  - research/artifacts/gottschalk-tarski-common-factor-residual-controls-2026-09-08.md
  - research/artifacts/gottschalk-common-factor-coset-collisions-2026-09-08.md
  - research/artifacts/gottschalk-stable-three-factor-reduction-2026-09-08.md
  - research/artifacts/gottschalk-recipient-affine-normal-form-and-fiber-obstruction-2026-09-08.md
  - research/artifacts/gottschalk-tarski-operand-reversal-exclusions-2026-09-08.md
  - research/artifacts/gottschalk-exact-quadratic-derivative-collision-criterion-2026-09-08.md
  - research/artifacts/gottschalk-central-odd-norm-conjugacy-direct-finiteness-2026-09-08.md
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

The full family `F=x+(1+R_t)R_s(x R_t x)` is now excluded over every
group: injectivity implies surjectivity. Infinite or even-order t
gives a bipartite operand graph; finite odd order gives an explicit
coset collision unless the memory subgroup is abelian. The Tarski
instance passes the earlier mask and coloring controls and still
has a finite collision. This closes that specified nonlinear family,
without asserting surjunctivity of the Tarski group or arbitrary CA.

The common-factor result extends to every outer actor `u` in `<t>`
for `F=x+(1+R_u)R_s(x R_t x)`. In the finite odd-order case,
injectivity forces either `u in <s>` or the memory subgroup `<s,t>`
to be finite abelian. For arbitrary `u`, a five-exclusion coset
witness gives further explicit collisions; it does not prove the
remaining rules injective. This family theorem is recorded in
`common-factor-power-actor-ca-are-surjunctive`.

A universal reduction is now recorded in
`stable-three-factor-reduction-proves-gottschalk`: add identity tracks
and compose with reversible local shears to reduce every finite-alphabet
CA to sums of products of at most three unary lookup factors over
`Z/qZ`. This preserves both injectivity and surjectivity in both
directions. Over finite fields there is also an ordinary cubic
polynomial version. The prerequisite
`three-factor-finite-alphabet-ca-are-surjunctive` is still open;
the existing block elimination theorems do not cover this universal
class. The reduction therefore does not close the headline goal.

The further universal normal form `H(x,u)=(x+u,F(x)-x-u)` puts
every output's nonlinearity on the opposite block while giving it
constant coefficient +1 or -1 on its own recipient track. The exact
fiber identity `H^-1(z,w) ~= F^-1(z+w)` shows that these properties
retain the full problem. Isolating a preserved certificate gives
fibers that are translates of F; none is known bijective independently.
The new prerequisite `recipient-affine-three-factor-ca-are-surjunctive`
is open. The artifact also excludes obtaining an invariant coordinate
fiber by constant linear two-track changes while retaining recipient
affinity for a non-affine rule.

In the conditional Tarski common-factor example, operand reversal
excludes two of the four residual mechanisms. At most two actors
remain for fixed noncommuting s,t, with exact subgroup relations in
the new artifact. They are necessary cases still to be tested, not
injective maps or counterexamples.

The quadratic difference equation now has an exact criterion for
every shared shift t, including orders one, two, and infinity.
For F=x+A(x R_t x) with arbitrary linear CA A, a collision exists
exactly when a configuration q yields nonzero delta=Aq and satisfies
the stated local compatibility and finite-cycle parity conditions.
Orbit recurrences then construct the two inputs. The criterion
also proves that the simplest one-subgroup mask cannot work in one
remaining Tarski case. An admissible nonzero q for either unresolved
case has not been constructed. The proved criterion is recorded in
`quadratic-shift-differences-have-exact-orbit-criterion`.

For each fixed Gamma, surjunctivity of the full family x+A Q_t on
Gamma x C_3, with arbitrary scalar linear A, is exactly equivalent
to direct finiteness of F_2[Gamma]. A local parity-majority involution
and two-block elimination prove sufficiency using only scalar direct
finiteness. The norm subclass proves necessity. This is recorded in
`central-c3-quadratic-surjunctivity-iff-direct-finiteness`;
neither side is established for arbitrary Gamma.

For any odd n>=3, the narrower central norm rules F_B=x+(B-I)E Q_t
on Gamma x C_n are explicitly conjugate to B on the parity coordinate
and identity on the other coordinates. This conjugacy preserves
composition and decoder identities. Finite central blocks also encode
arbitrary matrix rules on enlarged groups. The all-odd-cycle result
is recorded in `central-odd-norm-quadratic-ca-are-conjugate-to-linear`.
