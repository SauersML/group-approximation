# Static challenger and occurrence-local Hilbert--Schmidt breaker

**Date:** 2026-08-20  
**Status:** audited ingestion; no nonhyperlinear group is claimed.

## What was already present

The supplied notebook substantially overlaps established Cairn nodes:

- the dimension-reported recursion theorem is
  `dimension-matched-kleene-microstate-diagonal`;
- the same-model extraspecial breaker is
  `marked-clifford-table-exponential-dimension`;
- arbitrary predicates and a common hyperoctahedral type are already covered
  by `low-dimensional-hyperoctahedral-packet-groupifies-any-predicate` and
  `all-bcs-contexts-share-one-hyperoctahedral-signed-type`;
- the rank compiler and restriction doubling are
  `boolean-predicate-is-one-rank-jump` and
  `predicate-rank-gate-doubles-restriction-multiplicity`;
- the regular-trace and selector-induction fences, the Thompson--Clifford
  exact tape, the HNN circularity fence, and the finite-dimensional-only BCS
  decoder requirement were already represented in their dedicated nodes.

Those results were linked rather than duplicated.

## New exact reductions promoted

### Canonical-trace-conditioned diagonal

`trace-conditioned-dimension-matched-kleene-diagonal` proves that the
self-witness search may include finitely many strict trace/moment tests.  A
hyperlinear canonical-trace microstate must eventually pass them.  On a fixed
finite packet, near-regular traces give quantitative Plancherel multiplicities
by character orthogonality.  This is a local type-selection improvement, not
a global context-coherence theorem.

### Uniform bounded-area Clifford tape

`uniform-bounded-area-clifford-tables-force-mark-collapse` proves the exact
geometric closure criterion.  If every finite extraspecial multiplication
identity has area at most one constant `A` in a single finite presentation,
then a tuple of defect `epsilon` gives every `E_N` as an all-pairs
`A epsilon`-representation.  A surviving common mark would force the fixed
matrix dimension to exceed `2^N` for all `N`, so the mark is at most
`42A epsilon` from the identity.  The sole open construction is
`finitely-presented-uniform-area-clifford-tape`.

### Occurrence-local robust dimension games

`occurrence-local-dimension-games-force-mark-collapse` proves a weaker
closure theorem.  One need not derive complete Clifford multiplication
tables or identify all word names for a virtual observable.  It suffices that
each local test occurrence and each direct occurrence-consistency test be a
bounded-cost conjugate of finitely many prototypes, and that robust game
soundness force dimensions `D_N->infinity`.  The open finite-presentation
problem is isolated as `finite-orbit-occurrence-pauli-compiler`.

This route attacks the stabilizer-length obstruction semantically: local
occurrences remain separate until the game theorem decodes them globally.
High transitivity supplies finitely many equality-pattern orbits, but a real
construction must still encode the unbounded linear-code/Pauli incidence
family in finitely many bounded-arity orbits.

## Static-game provenance boundary

Lin's arXiv:2510.07162 establishes `MIP^co=coRE` and explicitly uses
synchronous compression and robust Pauli testing.  Cairn already records the
effective constant-gap fixed-point consequence as
`kleene-mipco-self-destroying-game`.  The stronger assertion that one named
theorem in the paper directly states the exact promise
`omega_co=1, omega_*=1/2` was not promoted here solely from the abstract or a
secondary paraphrase.  The construction does not need that stronger reading:
the established fixed-point game or the Fanizza finite BCS supplies the
static adversarial source, while the unsolved work remains its constant-HS
group transducer.

## Relation to the live Schur self-hash lane

The occurrence route is independent of the explicit paired-frame checksum.
In that lane, `paired-frame-forbidden-scalar-overlap-gap` already supplies an
amplification-independent local gap `1/98`.  The newest exact audit,
`gauge-symmetrizing-hard-pair-cancels-paired-overlap-gap`, shows that simply
forgetting private gauge orientation cancels this detector.  Thus the Schur
lane still needs a one-sided ownership label; the occurrence route instead
tries to avoid global ownership by making consistency an explicit local game
test.

## Additional integration from the expanded construction notebook

The expanded notebook's `SHST` interface is represented by the established
closure theorem `occurrence-local-dimension-games-force-mark-collapse` and
the open implementation `finite-orbit-occurrence-pauli-compiler`.  The graph
keeps the source-specific formulation: one fixed finite adversarial game or
the fixed Fanizza BCS is enough; no universal group machine or internal
dimension sensor is required.

Its stability shortcut is now recorded at the correct generality as
`hs-stability-plus-fd-residual-forces-nonhyperlinearity`.  This improves the
older minimally-almost-periodic special case: one nontrivial word killed by
all finite-dimensional unitary representations is sufficient.  The explicit
witness obligation is `finitely-presented-hs-stable-nontrivial-fd-residual`.

Finally, the occurrence-local philosophy suggested a concrete repair inside
the current Fanizza lane.  `thompson-site-pulses-localize-hard-exits` puts a
doubled finite hard packet at each independent Thompson site and uses its
factor swap as a transporter.  Earlier pulse signs live at different sites,
so prefix preservation is literal off-site commutation rather than a long
stabilizer comparison.  This removes the persistent-character tail problem
from that route.  The private-hard-share incidence was subsequently closed by
`fanizza-hard-exits-attach-to-thompson-site-pulses`.  The later audit below
identifies the remaining issue: the complementary active mass must itself be
placed under the next survivor prefix and attached to the next reducing
occurrence.

## Audit of the full construction notebook

The later full notebook was integrated by reference to the established
nodes above rather than copied into duplicate claims.  In particular:

- its dimension-reported and trace-conditioned fixed-point theorems are
  `dimension-matched-kleene-microstate-diagonal` and
  `trace-conditioned-dimension-matched-kleene-diagonal`;
- its exact Clifford breaker and bounded-area closure criterion are
  `marked-clifford-table-exponential-dimension` and
  `uniform-bounded-area-clifford-tables-force-mark-collapse`;
- its fixed-predicate finite packets are already subsumed by the stronger
  low-dimensional and balanced hyperoctahedral atlas nodes;
- its multiplicity-return, source-specific static transducer, and perfect-LCS
  endpoints remain open compiler interfaces, not existence proofs;
- its occurrence-name replacement is exactly the established closure theorem
  `occurrence-local-dimension-games-force-mark-collapse` with implementation
  hole `finite-orbit-occurrence-pauli-compiler`;
- its stability shortcut is
  `hs-stability-plus-fd-residual-forces-nonhyperlinearity`.

The notebook's strongest upstream Bell-separation phrasing was not used to
upgrade the root.  Cairn needs only an already recorded static adversarial
source; the unresolved mathematical work is the finite group-word decoder
with a dimension-independent normalized-HS modulus.

The same audit found and corrected one overclaim in the live S3 route.  A
free-occurrence HNN edge carries all four endpoint atoms but does not put the
returned three-atom union below the independent pulse survivor.  This is the
zero-defect fence
`free-occurrence-hnn-return-does-not-preserve-first-hit-prefix`, which
invalidates the former return route.  The replacement
`two-bit-tag-routing-splits-s3-exit-and-survivor` uses two commuting site tags:
one tag atom is the first-hit exit and the other three atoms are its analytic
survivor.  The only remaining local attachment is now
`tagged-s3-survivor-installs-next-recurrent-carrier`.

## Post-integration regular-trace audit

The later context-atom construction does close that local attachment:
`context-atom-tag-bridge-installs-child-carrier` transports a complete bounded
commuting context atom into the successor survivor, while routing the selected
tag atom into the first-hit exit.  This is a useful exact placement lemma.

It does **not** complete the Fanizza decoder.  The exact zero-defect first-hit
ledger is trace-functorial.  In the canonical finite von Neumann algebra it
would give nondecreasing recurrent trace together with a fixed positive exit
fraction at every level and a summable first-hit budget.  Hence the initial
carrier has trace zero.  This is the established fence
`exact-first-hit-ladder-kills-regular-carrier`, which invalidates both tagged
S3 return routes and the former pulse-decoder proof.

Accordingly the notebook's valid closure criteria split into two honest
matrix-only frontiers:

- the occurrence-game lane derives its contradiction from finite matrix
  dimension through `finite-orbit-occurrence-pauli-compiler`; it never asserts
  an exact positive-density ladder in every tracial representation;
- the explicit coefficient lane asks for
  `affine-leavitt-steinberg-hs-coefficient-decoder`, or equivalently a
  genuinely finite-matrix Schur/Reynolds overlap actuator, before applying
  cyclic trace or multiplicity pressure.

This distinction is load-bearing.  Static adversarial-source freezing,
canonical-trace side tests, local tag placement, and trace cyclicity are all
useful, but none alone supplies the finite-matrix-only asymmetry required to
separate microstates from the left regular representation.
