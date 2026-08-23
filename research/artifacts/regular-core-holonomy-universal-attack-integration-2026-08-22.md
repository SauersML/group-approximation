# Regular-core holonomy universal-attack integration — 2026-08-22

The supplied report is integrated by dependency rather than copied as a
second parallel programme.

| Report component | Cairn disposition |
|---|---|
| regular microstates and exact matrix ultraproduct representations | already covered by canonical-profile compactness nodes |
| regular-branch HS liftability | recorded in `regular-branch-liftability-plus-fd-kernel-forces-nonhyperlinear`, strictly weaker than all-profile HS stability |
| finite-subgroup regular-core theorem | recorded in `finite-subgroup-near-regular-has-large-regular-core`; it packages the existing Plancherel multiplicity theorem into one regular summand plus `o(d)` remainder |
| continuous multiplicity-commutant holonomy | already covered by `finite-group-shared-overlap-polar-alignment`, `canonical-finite-packet-data-stop-at-scalar-overlaps`, and `three-chart-loop-retains-free-multiplicity-holonomy` |
| qualitative synchronization compactifies to a finite gap | valid only if synchronization already excludes every canonical matrix-ultraproduct leak; this is `canonical-profile-word-collapse-one-window`, not a consequence of exact finite-dimensional collapse alone |
| factor universality plus factor-character rigidity | sound conditional implication, now `factor-universality-character-rigidity-implies-nonhyperlinear` |
| CDI supplies factor representation universality for every acylindrically hyperbolic source | correct; already audited in `cdi-property-t-envelope-has-nonabelian-base` |
| CDI plus regular/fd factor-character rigidity | impossible in that source class, but stronger than needed: `ah-groups-fail-regular-fd-character-rigidity` |
| Caprace--Thom character rigidity | stale v1 attribution; current v2 proves IRS rigidity and explicitly leaves character rigidity open, recorded in `caprace-thom-v2-leaves-km-character-rigidity-open` |
| Kac--Moody regular-core synchronization | retained as the precise open candidate `compact-hyperbolic-km-regular-microstates-synchronize` |
| Fell absorption erases a diagonally regularized payload | exact duplicate of `notes/FALSE_GAME_REPRESENTATION_REGULARIZATION_BY_FELL_ABSORPTION.md` and `free-label-orthogonalization-erases-payload-trace` |
| retaining label and payload families exposes noncanonical payload words | already covered by `free-label-orthogonalization-erases-payload-trace`; the objection requires some nonidentity payload word with nonzero payload trace |
| non-CE algebra in a canonical group-factor corner | exact duplicate of `nonce-factor-in-group-factor-corner-forces-nonhyperlinear`; the unrestricted existential version is goal-equivalent |

## Net mathematical change

The genuinely useful reduction is local-to-global.  On each finite subgroup,
canonical trace forces Plancherel multiplicities and hence a regular core on
`1-o(1)` of the space.  This does not solve the approximation problem: exact
overlap identifications differ by unitaries in growing multiplicity
commutants, and cycle products survive as holonomy.  The new candidate route
asks the native Kac--Moody two-cells to kill those holonomies on the regular
branch.

The factor route is also sharpened.  Universality plus full factor-character
rigidity would indeed be terminal, but it cannot be obtained by simply
choosing the same acylindrically hyperbolic source in the CDI theorem.  Such a
source has a proper infinite ICC quotient, whose pulled-back regular
character is already an extremal diffuse nonregular character.  The exact
CDI bridge is weaker: after dividing by the actual representation kernel,
its distinguished character is faithful, so it is enough to classify only
**faithful** nonregular factorial characters.  The quotient-character
counterexamples are nonfaithful and do not touch this restricted face.  This
strict narrowing is recorded in
`cdi-image-quotient-off-regular-characters-are-ce`.

## Expanded-report deduplication

The later expanded universal-attack report adds proofs and constants but no
new independent dependency.  Its sections compact as follows.

- The ultraproduct equivalence and qualitative-to-finite-gap arguments are
  instances of the existing canonical-profile compactness layer.
- Regular-branch liftability, the finite-dimensional residual kernel
  contradiction, and the finitely generated residual-finiteness corollary
  are all carried by
  `regular-branch-liftability-plus-fd-kernel-forces-nonhyperlinear`.
- The finite-subgroup character calculation is the proof content of
  `finite-subgroup-near-regular-has-large-regular-core`.  Allowing a flexible
  `o(d)` dimension change is sufficient and avoids adding a stronger
  same-dimension stability assertion that the downstream route does not use.
- Blindness of local character and multiplicity data to relative chart
  position is already the multiplicity-commutant holonomy cluster cited in
  the table above.  The proposed spanning-tree gauge normal form is a useful
  description of the open node, not a new solution of it.
- Fell absorption, the exposed-payload-word objection, and the non-CE
  group-factor corner criterion remain exact duplicates of the earlier
  trace-promotion nodes.

Accordingly Cairn records one open Kac--Moody synchronization claim rather
than duplicating the report's Definitions 2.1, 5.1, and finite-dimensional
Holonomy Problem as parallel aliases.  A proof of that node would have large
cascade value: simplicity supplies the finite-dimensional residual kernel,
and regular-branch liftability then reaches the nonhyperlinear-group goal in
one step.

## Source correction

The report cited the June 2026 v1 abstract of arXiv:2606.27993.  The current
July v2 is joint work of Caprace--Thom, is completely rewritten, and removes
the character-rigidity theorem.  Corollary 5.3 concerns invariant random
subgroups; Remark 5.4 leaves absence of nontrivial characters conditional on
an unchecked square-integrability statement.  Cairn therefore does not use
the superseded v1 claim.
