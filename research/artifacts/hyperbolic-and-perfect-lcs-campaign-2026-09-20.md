# Hyperbolic residual finiteness and perfect-completeness linear games

Date: 2026-09-20. This is the next targeted research wave after the Liu
consequence integration. The two requested existence/hardness targets remain
OPEN unless a complete new proof is supplied. Graph statuses are not Lean
or external human proof certification.

## Exact goals and source gate

The geometric target is the existing
`non-residually-finite-hyperbolic-group`. It asks for a word-hyperbolic
group with a nonidentity element killed in every finite quotient. It does
not require nonsoficity or nonhyperlinearity. Current primary-source
context was rechecked against
[Wilton, with an appendix by Sisto](https://arxiv.org/abs/2410.00556) and the sources
in the preceding hyperbolic campaign; no solution is inferred from a
finite quotient search or an unproved stability hypothesis.

The quantum target is now explicitly named
`lcs-perfect-quantum-completeness-re-hardness`. Its source is
[Taller--Vidick v2](https://arxiv.org/html/2507.22444v2), particularly
Section 5 and the discussion of perfect completeness. Their reduction
has a fixed positive completeness loss; the endpoint sought here has
halting quantum value one and nonhalting value bounded by one fixed s<1.
The source also distinguishes synchronous from unrestricted quantum value.
This wave checks the actual endpoint rather than relabelling the older
weak commuting-completeness compiler as a hardness theorem.

## Three independent lanes

- Hyperbolic: test finite central detectors with elementary-abelian radical,
  beyond the preceding composition-factor exclusions. Existing concurrent
  GHB7 and triangle-matching work is read and reused, not overwritten.
- Linear test: examine the zero-noise Fourier decoding step, including
  globally compatible cheating strategies rather than isolated local cells.
- Halting switch: test whether the fixed Liu-based killed-mark seed can
  be inserted only on nonhalting inputs without violating computability.

Root coordination checks theorem interfaces, quantitative normalizations,
and exact source scopes. Any computation is remote on MSI, bounded and
single-core unless an explicit reason and resource check justify more.

## Completeness, gap, and efficiency are separate obligations

The new root uses the supremum over finite-dimensional entangled strategies.
Its halting value one is not the same as merely having a commuting strategy,
and does not require exact finite-dimensional attainment. The existing
Leavitt sign construction is excellent for a fixed qc/qa separation but
does not give the required positive quantum branch.

There are two additional distinctions:

1. A strictly positive loss depending on the input is not a constant
   soundness gap. Compactness for each individual game does not give one
   constant for a machine-indexed family.
2. A total computable algorithm emitting each finite game is weaker than
   polynomial-time succinct sampling and verification with bounded answer
   length. Exhaustively expanding a succinct verifier is computable, so the
   strong root implies the old weak compiler; the converse is not supplied.

The standard upper inclusion in RE uses only a separated threshold: pick
a rational r with s<r<1, enumerate finite dimensions, and search for a
finite-dimensional strategy with value greater than r. For a rational
finite game this is a semialgebraic existence problem in each fixed
dimension (real and imaginary parts of states and measurement matrices).
The strict inequality and density of computable approximations also give
a direct witness search. On halting inputs such a witness exists because
the supremum is one; on nonhalting inputs none does. No computable bound
on the required dimension is asserted. Thus perfect completeness means
a value statement, not an effective finite-dimensional bound.

## Attribution and certificate boundary

Taller and Vidick own the entangled long-code reduction and its source
analysis; the earlier BCS hardness and repetition inputs retain their
authors. Jihao Liu's internality, Andreas Thom's conditional normalization,
and the repository's credited Leavitt calculations supply the fixed seed
used in the switching experiment. They do not prove perfect-completeness
hardness. The hyperbolic central-extension strategy retains its separate
Dogon--Vigdorovich and cohomological premises.

A failed subclass is a route obstruction, never a proof that either
major open target is false.

## Results of the three lanes

### 1. A finite-quotient obstruction for the hyperbolic construction

[[hrf-next-affine-radicals-preserve-detector-image]] proves that a split
elementary-abelian p-radical adds no detectable edge twists under two
explicit first-cohomology vanishing hypotheses. The proof decomposes
central extensions into inflated base classes and invariant alternating
forms, then shows that the latter have zero edge discrepancy. It does
not classify all finite quotients or prove persistence. The written
proof is [here](hrf-next-attack-2026-09-20.md).

The next useful targets are the omitted mixed H^1 classes, nontrivial
vertex affine cocycles, and nonsplit or nonabelian radicals. A search
restricted to the covered split quotients cannot settle the universal
finite-quotient condition. This theorem is algebraic; it does not use
Liu's internality theorem or assert a new stability theorem.

### 2. The unchanged zero-noise linear test has a global counterexample

[[lcs-pc-zero-noise-coloring-cheat]] uses the three-colouring game of K4.
Its unrestricted quantum value is at most 11/12; the associated repeated
projection game's value tends to zero. Nevertheless the noiseless TV
output has a perfect classical strategy at every repetition count.
The strategy is one globally consistent assignment, not a collection
of incompatible local witnesses. The full proof and exact source
interfaces are [here](lcs-perfect-completeness-attack-2026-09-20.md).

This closes the proposed generic zero-noise decoder attack. It leaves
open a source-specific reduction or a changed test that defeats these
odd-support strategies while preserving perfect quantum completeness.

### 3. Finite bad seeds cannot implement the whole nonhalting branch

[[lcs-switch-marked-seed-transport-is-re]] proves a computability
obstruction. For any recursively enumerable library of finitely
presented killed-mark seeds, membership in the normal closure of their
transported marks is recursively enumerable. If every nonhalting output
sign had such a certificate, and every halting output had a matrix model
preserving its sign, these certificates would enumerate coHALT.
This remains impossible when the maps are chosen noncomputably and
have unbounded word length. The proof is
[here](lcs-halting-switch-audit-2026-09-20.md).

Thus a fixed Liu-based seed supplies the separating example but cannot
by this finite transport mechanism supply all negative instances of the
desired hardness reduction. A successful reduction needs a negative
obstruction not exhausted by that certificate language, as well as a
uniform quantitative gap and the stated efficiency.

## Review and integration record

The root checked all three written arguments. A sibling independently
checked the unrestricted K4 bound and all raw-query identifications
against the TV definitions, and checked the affine-extension
decomposition and its edge-phase identity. The other sibling checked
the seed-switch enumeration and the exact efficient quantum-completeness
endpoint; the weak-interface conversion explicitly discards unsampled
constraints. No flaw was found in these
bounded reviews. These are internal mathematical reviews, not Lean or
external human verification, and no literature-priority claim is made.

Only this wave's owned files are staged. Concurrent hyperbolic and Lean
work is preserved and excluded from this wave's source snapshot. Graph
validation is performed on MSI against the pinned staged tree; its
report records the source revision, statuses, and limitations separately.
Both requested main targets remain OPEN.

The [MSI validation report](hyperbolic-perfect-lcs-validation-2026-09-20.json)
checks source commit `4270d69824` through its identical pinned tree
`691d67618066fb77d7546c09b353bb25706099e3`: 34,237 canonical nodes,
zero schema errors, no duplicate findings for this wave, and all three
new auxiliary claims ESTABLISHED. The two main targets remain OPEN.
The check took 8.548 seconds on one CPU at low priority on acn112, using
the existing Cairn kernel. No Lean or local build ran; the report states
the direct parser/linter/compiler check's deviation from the full CLI.

## Constructive continuation and stronger decoder audit

The next parallel pass supplies a positive intermediate theorem, not a
solution of either main target.

1. The [weighted conjugacy compiler](lcs-constructive-compiler-2026-09-20.md)
   converts bounded linear-and-conjugacy constraints on involutions into
   binary LCS games. It preserves matrix-energy infimum zero as quantum
   value one, and transfers a uniform positive energy gap to a uniform
   unrestricted quantum gap. Its exact extensions use dimension 4d.
   Slofstra's conjugacy gadgets and Culf's quantitative tracial rounding
   are named inputs, not attributed to this repository. The succinct
   interface separately checks bounded fair-bit sampling and uniform
   variable queries. The new OPEN source node is
   `lcs-weighted-conjugacy-halting-gap-source`: no machine-to-source
   construction is supplied by the compiler itself.
2. The [shared-anchor attack](lcs-anchored-attack-2026-09-20.md) gives an
   exact globally compatible finite-dimensional model for the proposed
   Pauli splitter repair on K4, including shared marginals and the full
   local Boolean commutator table. Tensor repetition retains the cheat.
   This excludes that specific changed test, not all non-affine tests.
3. The [CE quotient audit](ce-affine-quotient-audit-2026-09-20.md) strengthens
   the earlier affine-decoder obstruction. One positive CE corner model
   already supplies a hyperlinear quotient and a canonical character
   corner with affine context supports. Therefore merely choosing a
   nonhyperlinear ambient group cannot rescue universally CE-exact
   affine decoding on an affine-unsafe positive source. The older weaker
   theorem remains true; its optimistic escape discussion is corrected.
   Liu's theorem is not used in this new obstruction.
4. The [five-dimensional detector proof](hrf-breakthrough-2026-09-20.md)
   excludes every nonzero five-twist of the pinned PSL2(19) triangle when
   all three vertices are conjugate to Sym4 in characteristic 19. All
   124 cases have explicit polynomial unit-ideal certificates, so the
   conclusion holds over the algebraic closure, not just a finite list
   of fields. This does not control other representations or all finite
   quotients. A separate Heisenberg countermodel explains why abstract
   perfect-kernel and minimal-detector conditions cannot eliminate
   noncentral solvable radicals without using the actual vertex maps.

The compiler and CE argument have independent internal written reviews;
the detector certificates have exact remote arithmetic verification.
These checks are not formal proof certification or a literature-priority
claim. Neither a persistent hyperbolic class nor the required halting
source family has been constructed. Both main targets remain OPEN.

The [constructive-wave MSI report](constructive-lcs-detector-validation-2026-09-20.json)
pins source commit `ea0a876529` and tree
`4ff0947a70e9d65307a7b8875189c3667c781f59`: 34,247 canonical nodes,
zero schema errors, no duplicate findings, ten added nodes, and no status
changes among pre-existing nodes. The four new auxiliary claims are
ESTABLISHED; both targets and the weighted halting source remain OPEN.
The standard parser/linter/compiler check took 8.175 seconds on one
low-priority MSI CPU. The report retains the full-CLI and proof-review
limitations.

## Uniform amplification and global source audits

The [amplified detector proof](hrf-amplified-2026-09-20.md) now excludes
all positive multiplicities of Sym4, not just the five-dimensional
case. A legitimate vertex gauge normalizes two multiplicity blocks;
four linear eliminations and a sixteen-product multiplication table
then force a linear combination of associators to equal the unit.
The noncommuting blocks never enter a commutative polynomial certificate.
All 124 nonzero twists have input-bound certificates. The independent
MSI arithmetic verifier took 1.2731 seconds; a separate source/proof
review passed. These are not Lean or external human verification.

The [extension-rigidity proof](hrf-sym4-extension-rigidity-2026-09-20.md)
proves H1(S,End(Sym4))=0 in characteristic 19 by explicit polarization
and Sylow-normalizer cohomology. Thus every module with only Sym4
composition factors splits. Restricting a representation to an
eigenspace of its central order-five mark combines these results:
`hrf-sym4-composition-sector-kills-five-mark` eliminates the whole pure
composition sector without assuming scalar mark or semisimplicity.
Mixed constituents and other characteristics remain uncontrolled.

For the quantum source, the [controlled-port audit](lcs-auth-controlled-form-audit-2026-09-20.md)
and [Toffoli audit](../../notes/lcs-source-toffoli-word-semantics-audit-2026-09-20.md)
show why even completing the entire circuit group's word theory does
not authenticate the desired nonlinear semantics. Triple tensoring
preserves all those relations and central characters but creates a
fixed positive literal-decoder defect. Proper-corner and non-word
readouts remain possible; neither a uniformly positive retained mass
nor a complete HALT-positive source has been obtained. Both root
problems remain OPEN.

The [amplification-wave validation report](amplified-detector-source-validation-2026-09-20.json)
binds commit `e6c57d4ad3` to tree
`1fd09b13980716fa99de049103a83c6aff7755ff`. Its 34,283-node snapshot
has zero schema errors and no duplicate findings. Compared with the
independently checked immediately preceding committed snapshot, six
nodes were added and no existing node status changed. Both main roots
and the weighted halting source remain OPEN. Validation took 8.283
seconds on one low-priority MSI CPU; the report states the exact
parser/compiler scope and absence of full-CLI or Lean verification.

## Beyond the pure sector: low degrees and common corners

The [mixed spectral reduction](hrf-mixed-spectral-balance-2026-09-20.md)
uses conjugacy to inverses and one nonzero twist to force uniform
order-five spectra in every characteristic other than five. In
characteristic 19 it gives two exact integer equations on arbitrary
vertex composition factors, without semisimplicity. The first mixed
types in dimension ten are L0+L8 and L2+L6; neither is claimed to
extend to a detector.

Combining this with the elementary nine-character orbit of the
order-nineteen root subgroup proves the
[all-field degree-nine obstruction](hrf-mixed-nine-dimensional-obstruction-2026-09-20.md):
every representation of a nonzero pinned twist of dimension at most
nine kills the mark, in every characteristic. The characteristic-five
case uses perfectness and Schur's lemma rather than a nonexistent
nontrivial fifth-root eigenspace. Actual degree-five linear/unitary
detectors are excluded; abstract projective extensions and larger
finite detectors are not silently included.

The [proper-corner audit](lcs-auth-proper-corner-audit-2026-09-20.md)
first proves that a single atom retains a corner of weight at least
1/4, correcting an overly broad reading of the tensor obstruction.
It then gives three explicit rational-complex rank-one controls
whose port group has projective closure PU(4). Scalar-preserving
exact amplifications of this model force common reducing corners
with literal controlled-port semantics to have weight tending to zero.
For finitely many disjoint conjugates the explicit estimate is
tr(P)<=3/N+9 beta^m, beta<1, with an approximate version as well.
The density and quantitative arguments passed independent internal
review. They do not exclude new observables or nonreducing decoders,
and supply no HALT-positive source. Both main targets remain OPEN.

The [mixed-detector/common-corner validation report](mixed-detector-corner-validation-2026-09-20.json)
binds commit `2d55562521` to tree
`21a8978fd6829f8f307902c8ec72b667baf90423`: 34,289 nodes, six added
nodes, zero schema errors, no duplicates, and no pre-existing status
changes. Its one-CPU MSI check took 8.720 seconds. The three new
claims are ESTABLISHED; both main roots and the weighted halting
source remain OPEN. New mathematics in this tranche is symbolic,
not a newly run numerical search.

Next constructive tests: on the triangle side, the first unexcluded
characteristic-19 mixed placements have dimension ten, with vertex
types drawn from 2L4, L0+L8, and L2+L6, not all 2L4. On the source
side, a genuinely different decoder must avoid requiring a uniformly
positive corner reducing all the fixed controlled ports while preserving
every honest model. Neither this particular model-preservation property
nor reduction of these ports follows from bare YES-instance completeness.
