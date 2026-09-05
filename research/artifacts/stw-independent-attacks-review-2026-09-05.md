# Review of the finite-abelian, cancellation, Fock, and corrected-word proofs

Date: 5 September 2026. This records internal mathematical review of
four distinct lines of work. The named-problem count remains one
internally reviewed solution manuscript, LIX. No external peer review,
formal verification, or further named-problem resolution is claimed.

## Finite abelian component groups

The root proof constructs every finite abelian group as the entire
unitary component group of a simple stably finite AH algebra with
zero K1. The separate
[independent review](stw59-finite-abelian-independent-review-2026-09-05.md)
read both the new joined-base proof and its gauge/cyclic prerequisites.
It found no gap in the ten stated checks. In particular, each reduced
K0 attaining class extends globally and vanishes on the other arms;
the Euler image is the direct sum of the prescribed integer lattices.
This excludes a hidden relation that an armwise calculation alone
would not exclude. The review also checks actual bundle gluing and
first matrix stabilization of the commuting generators.

## Compact-summand cancellation

The root reviewed the complete
[cancellation proof](stw99-lxxvi-rr0-compact-summand-cancellation-2026-09-05.md).
The strict relative theorem is used on X times an interval with both
endpoint p-frames prescribed. On the clopen zero-target locus the
remaining source projection is zero by finiteness, so no unjustified
strictness assertion is made there. Polar transport cancels the
projection bundle summand.

The separate local support lemma uses a continuous projection type
and finite projection equivalence to identify the whole fiber support;
it does not infer a uniform gap merely from fiberwise compactness.
The closed cutoff core then has two actual projection bundles, while
its complement has strict positive comparison. The Cu-limit argument
keeps the compact summand at a common stage and uses two successive
way-below comparisons before cancellation. The final image-removal
argument extracts an actual compact projection submodule from a
source positive module and cancels its target image. No section-algebra
stable-rank-one hypothesis was inserted at any step.

## A Toeplitz obstruction beyond proper coefficient corners

The root reviewed the complete
[mixed Fock proof](stw61-mixed-semicircular-defect-complete-obstruction-2026-09-05.md).
The left/right creation commutator errors cancel on the vacuum. Borel
functional calculus is used only inside a Hilbert-space representation.
The sign operator has zero vacuum expectation and moves that vector
entirely into the first left range, proving a norm-one lower bound.
Its Toeplitz defect is nonzero. The represented mixed algebra commutes
with this sign operator, but the represented test projection does not.

For the support assertion, scalar evaluations at plus and minus one
use the faithful coefficient Fock representation. The two omitted
Wold lines are distinct for every nonzero real parameter, since an
exponential cannot be constant on an interval of spectral measure.
Their range projections have join one. This excludes every proper
coefficient upper projection and every scalar functional translate,
and the explicit compressions meet the defect and both ranges.
The theorem concerns the specified mixed generated algebra, not all
unitaries in the free product.

## Corrected word spaces and homotopy lifting

The root reviewed the
[overlap-corrected word-space proof](stw58-overlap-corrected-word-spaces-and-homotopy-lifting-2026-09-05.md).
The transfer formula is a genuine right action for the product group:
successive transfers multiply in each coordinate in the correct order.
The Borel associated-bundle sequence includes the component-group
terms. The injective difference map removes their possible obstruction
to the degree-one cokernel calculation. Degree zero is explicitly a
component orbit-set identification, not an unprovided group structure
on the Borel quotient.

The finite-padding lift telescopes multiplicative increments in their
displayed order. Its append operation is equivariant for the original
transfer group embedded in the enlarged group, so it does not require
a global representative of the initial Borel lift. The fixed added
coordinates preserve stationary subfamilies exactly. Neither the
correct domain homotopy groups nor this homotopy-lifting operation
proves connectivity of the remaining multiplication fiber.

## Verification boundary

Cairn graph checks validate schema, dependencies, and derived statuses;
they do not verify these mathematical proofs. Native checks are run
only on MSI against the relevant dependency closure. Results for this
integration are recorded here after those commands complete. Concurrent
unrelated repository changes are outside the validation claim.

Both native commands passed for this batch:
`/usr/bin/python3.11 tools/cairn.py check --changed` and
`/usr/bin/python3.11 tools/cairn.py preview`.
The relevant closure contains 67 nodes (35 claims and 32 routes).
The finite-abelian, compact-cancellation, and mixed-semicircular
claims derived as established. LIX remained refuted in the graph;
LVIII, LXI, and LXXVI remained open.

The MSI logs are `proof-batch-check.log` and
`proof-batch-preview.log` under
`/projects/standard/hsiehph/sauer354/stw79-cairn-check-20260904/cu-all-base-scope-20260905/`.
These files are replaced by subsequent scoped validation runs.

## Compatible stable surjectivity and function algebras

The final deduction in this round is
[compatible split stable surjectivity](stw58-compatible-split-stable-surjectivity-2026-09-05.md).
The root proposed the deduction and independently reviewed the complete
written proof. For each positive homotopy degree, one fixed full
hereditary matrix piece has its unitary homotopy groups already in
the stable range at every matrix size. Inverting its canonical stable
maps and composing with inclusion gives compatible group sections.
Only one nonzero endpoint is needed; the other endpoint and overlap
may vanish. The direct-sum description of the remaining kernels is
group-theoretic and does not assert continuous sections of spaces.

The function-algebra corollary reduces a matrix unitary to finitely
many scalar coordinates with compact joint range. The matrix size
can then exceed the stable-rank bound for that coordinate range.
The split scalar quotient handles a nonunital hereditary coefficient.
Full hereditary inclusion transfers its size-one K1 representative
back to the original function algebra. Normalization at infinity
uses actual degree-zero K1-injectivity of B and the split evaluation
extension. This proves K1-surjectivity for every locally compact
Hausdorff base, without asserting purity or K1-injectivity of the
function algebra.

The [degree-one source supplement](stw58-degree-one-primary-citation-audit-2026-09-05.md)
records a separate verified loop-surjectivity proof and the newer
CGSTW citation cross-check. The original Rieffel scan was rendered
on MSI and visually read by both the root and the unitary-group agent.
Its all-torus hypothesis is not replaced by stable rank one. The
supplement preserves the existing note's distinction between later
published degree-one assertions and the injectivity derivation that
has not been verified here. Rechecking that citation is not counted
as a new theorem or an open-problem resolution.

After integrating compatible split stable surjectivity and the source
supplement, both native `check --changed` and `preview` passed on MSI
for the expanded closure of 71 nodes (37 claims and 34 routes).
The new split-surjectivity claim derived as established; LIX remained
refuted and LVIII, LXI, and LXXVI remained open. These are scoped
research-graph checks, not formal verification of the mathematics.
