# Closing the complete Theorem E formalization

Baseline: 2026-09-06, proof tip `02d72c87f78aca950507f38483f740e28908e0c2`,
based on main `0767babffd2d32e5745a6bc49b3ba6ebddd21c8a`.
Working draft: [PR #195](https://github.com/SauersML/group-approximation/pull/195).
This plan covers the entire Theorem E dependency chain, called Theorem C in Lean.
It does not claim that the formalization is complete.

## The finish line

Both existing endpoints in `TheoremCAssembly.lean` must pass
`#audit_closed_axioms` without changing their advertised propositions:

- `TheoremC.manuscriptTorsionFreeFullMFRadical_closed : PrintedTorsionFreeFullMFRadical`;
- `TheoremC.manuscriptTorsionFreeSimplified_closed : PrintedTorsionFreeSimplified`.

Their full namespace is `GroupApproximation.Manuscript.NonMF`. The permitted
axioms are exactly `propext`, `Classical.choice`, and `Quot.sound`. A new
certificate structure without an inhabitant, an extra leading hypothesis, or
moving an admission to another file does not discharge an obligation.

The current combined lane build passes. A fresh Lean traversal of the actual
proof dependencies of both endpoints finds exactly the five direct admissions
below; their axiom closures contain the three permitted axioms and `sorryAx`.
The strict source scan independently reports the same five placeholders.
Thus there are no additional admission leaves hidden in the current imported
endpoint proofs, although the proposed reductions below have further unproved
inputs. A successful build does not establish completion.

## All remaining work, including the hidden inputs

| Package | Current assembly admission | What must actually be proved | Completion evidence |
|---|---|---|---|
| DGO polygon geometry | `dgoProposition414Uniform`, placeholder line 147 | Both uniform bounds for arbitrary multiplicative quasigeodesic constant and every polygon size; then discharge the existing DGO 4.21(b) and joint-family-selection consumers | Original `DGOProposition414Uniform` and `DGOLemma421b` pass closed axiom audits |
| Osin diagram construction | `estimatingSelectionConstruction`, line 244 | Construct the reduced O-equivalent diagram, its estimating scaffold, and graph from the source hypotheses | A proved construction at parameters shared with the unbound estimate |
| Osin uncovered boundary estimate | `estimatingUnboundOutput`, line 254 | Replace the false universal-parameter interface by the actual synchronized parameter choice, then prove complementary-region surgery and the arc budget | Closed relative Greendlinger and Hull 4.9 inputs; original refutation retained |
| Hull joint-family preservation | `hullLemma44FamilyInclusionJoint`, line 214 | Greendlinger **plus** relative-isoperimetric transfer **plus** relator respelling, with one compatible order of constants | Original joint-family Lemma 4.4, including ball injectivity and all family-preservation clauses, passes the closed audit |
| Concrete starting group | `kotowskiOllivier`, line 381 | An actual infinite, finitely presented, torsion-free hyperbolic group with property (T) | Original `Hyperbolic.SharpExistence` passes the closed audit |

The first four packages feed Hull's canonical quotient, one-step construction,
Theorem 7.1, and the common-quotient and Fournier-Facio inputs. The last package
supplies their starting group. Together with the existing Chiodo/Higman and
Minasyan–Osin proofs, these feed `literatureInputs`, `hullInputs`, and both printed
endpoints. All of these consumers must be audited when their inputs close.

## DGO: extend the completed geometry to the actual uniform theorem

Already proved: the full additive case of Proposition 4.14, closed Lemma
4.21(a), the conditional full proof of 4.21(b), and the general-parameter
short-isolating-cycle construction for four-gons.

The missing step is the arbitrary-polygon **linear sum bound** at general
multiplicative constant. `DGOPolygonSideCountAll` gives a quadratic individual
bound from a four-gon base case; this alone cannot discharge Proposition 4.14.

1. Parameterize the existing balanced-surgery development coherently. Carry
   the original quasigeodesic inequalities through cuts, recuts, connector
   bounds, and the complete isolated-component families. Retain the additive
   API as a specialization; do not duplicate the entire module chain.
2. Use `DGOShortIsolatingCycleGeneral` for the general base cases and the
   existing Morse-based chord selection for the balanced split. Prove the
   subdivision recurrence and its linear bound with a constant chosen before
   the polygon size. Derive the individual bound using the existing collapse
   and recut argument.
3. Instantiate both original consumers and audit them. The finite-size bound
   needed by 4.21(b) can close earlier: its counting proof uses polygons with
   at most six sides and the already proved `(1,1)` sum bound. Treat that as
   an integration checkpoint, not as completion of general 4.14.

The proposed additive comparison for multiplicative constant greater than one
is refuted in [#199](https://github.com/SauersML/group-approximation/issues/199).
It must not re-enter this route under another name.

## Osin: prove selection and the budget as one construction

The present unbound-output proposition is false even with the advertised
hyperbolicity, small-cancellation, and numerical range hypotheses; see the
closed counterexamples in
[#198](https://github.com/SauersML/group-approximation/issues/198).
Filling that literal proof hole is impossible in a consistent formalization.

The repair must preserve the final theorem and the original proposition with
its refutation. Add a source-faithful producer with this order of choices:
ambient geometry and quasigeodesic constants; geometric closeness/density
constants; epsilon; sufficiently large rho; relators; input diagram; output
diagram with **both** selection and unbound data.

`UnboundParameters.lean` proves the numerical choices after the geometric
constants are supplied. It does not construct those constants or the regions.
The outstanding proofs are:

1. Derive the geometric constants from the ambient hypotheses and reconcile
   the published and preprint numbering against the source argument.
2. Prove the local replacement underlying `SelectionFaceDropOracle`; use the
   existing well-founded face-count descent to build the scaffold.
3. Construct the complementary regions and their actual boundary incidence
   partition; prove cutting-path shortening, the density estimate, and the
   unbound-arc count. Preserve O-equivalence, reduction, boundary words, and
   the required nonempty relator-cell condition throughout.
4. Feed the same chosen parameters to the estimating-data assembly, the
   relative Greendlinger theorem, and Hull 4.9. Keep the proved cyclic-rotation
   correction in the exterior-arc consumers.

A package accepting the missing partition or face-drop oracle as a hypothesis
is an intermediate reduction only. The milestone is the actual producer and
its audited geometric consumer.

## Hull 4.4: discharge the additional geometry, not just the wrapper

`HullSCLemma44FamilyAssembly` reduces the joint statement to three inputs:
`RelativeGreendlingerStatement`, `RelativeIsoperimetricBridgeStatement`, and
`HullRelatorRespellingStatement`.

The first is supplied by the Osin package. The other two are still mathematical
work. The relative-area induction already exists, but the passage from its
linear kernel-area bound to quotient hyperbolicity and proper peripheral
metrics remains an input (`RelativeLinearAreaTransferStatement`, or the
equivalent Dehn-transfer route). Prove the relative-presentation argument and
its finite peripheral-support control.

For respelling, `HullSCLemma44JointRelabel` proves a joint transport only under
additional alphabet/base-containment conditions. The original-family
respelling is still an input, and those conditions must be derived in the
actual construction. Audit this proposed intermediate statement against the
source before extending its proof chain. If it is too strong, report the
counterexample and use a justified direct joint-diagram argument while retaining
the original final Lemma 4.4 proposition.

Finish by assembling ball injectivity and preservation of the selected,
original, and joint families in the same canonical quotient. Proving just
the selected-family special case leaves the downstream Osin construction open.

## Starting group: validate a concrete candidate before investing further

Recommended candidate for feasibility work: the explicit group
`G_HB₂^(2)(7)` from Caprace–Conder–Kaluba–Witzel, followed by a torsion-free
finite-index subgroup. Their Theorem 3.1, Proposition 7.3, Corollary 7.8, and
Proposition 7.15 supply the relevant geometry, angle criterion, and finite
matrix representation. See the [primary paper](https://arxiv.org/abs/2011.09276).

The accompanying [exact Python experiment](../../GGT/Experiments/theorem_e_triangle_seed.py)
checks all 11 defining relators in four-by-four matrices over F₇ and computes
the three pair-image orders as 343, 2401, and 2401. This is reproducible
exploration, **not a Lean certificate or a proof of a torsion-free kernel**.

The finite-index transfer of property (T), finite presentation, and
hyperbolicity is already proved in
`Kazhdan/SharpExistenceLatticeUnconditional.lean`. Despite its name,
`Hyperbolic.LatticeRouteInput` does not require a Lie lattice: an appropriate
concrete group and subgroup suffice. Its unconditional assembly therefore
reuses all three permanence results.

The candidate still needs substantial formal work:

- Prove its finite vertex-group presentations, the matrix homomorphism, and
  injectivity on those vertex groups from exact finite data.
- Prove the relevant triangle-of-groups developability and curvature results,
  infinitude, and conjugacy of finite-order elements into vertex groups.
  Existing disc-diagram and slim-triangle work may help, but no complete
  applicable triangle-of-groups/CAT(-1) theorem was located. A specialized
  combinatorial proof is worth evaluating before building general metric
  foundations; it is not an already available shortcut.
- Prove the three-subgroup property-(T) criterion and the required finite
  angle bounds, reusing the fixed-space/orthogonality machinery; alternatively
  produce and replay an actual exact Hodge certificate. Neither certificate
  production nor the complete criterion has been discharged for this group.
- Construct the finite-index kernel, prove it torsion-free and infinite, and
  instantiate `LatticeRouteInput` to obtain the unchanged `SharpExistence`.

This route has concrete finite data, but its full Lean feasibility is not yet
established. Its geometry and analytic criterion need explicit proof outlines
before committing to a large implementation. The existing generalized-
quadrangle table route also lacks an exhibited suitable table; moreover its
legacy degree-only torsion-freeness certificate is false, reported immediately
as [#200](https://github.com/SauersML/group-approximation/issues/200).

Changing the starting group to merely acylindrically hyperbolic is not a
drop-in replacement: current Fournier-Facio and common-quotient inputs consume
a hyperbolic group. Preserve the existing target by default. Any different
mathematical route needs an explicit replacement proof and review by Sauers.

## Execution order and evidence of progress

First settle the routes that could invalidate the entire schedule: the joint
Osin parameter interface, the Hull respelling/transfer hypotheses, and the
concrete seed's geometry and property-(T) proof outlines. This is a bounded
design checkpoint: each must have its exact hypotheses, existing reusable
lemmas, missing constructive steps, and a source-backed mathematical argument.
A new name for the same missing conclusion does not pass it.

Then close complete packages: general DGO geometry; the synchronized Osin
construction and its Greendlinger/Hull 4.9 consumers; Hull 4.4's remaining
controls; the concrete seed; the final assembly. These have distinct proof
boundaries suitable for coordinated contributors, but this plan does not
assume additional agents or assign anyone work.

For every implementation session, report the specific unproved input removed,
the assembly consumer it reaches, and that consumer's remaining axiom closure.
Supporting lemmas are valuable when their connection to a listed obligation
is explicit. Module counts and successful incremental builds are not measures
of completed formalization. Keep all work on the tip draft PR; immediately file
new counterexamples and update this ledger when a route changes.

Coordinate with Sauers before editing outside the handoff's `GGT/` and
`Manuscript/NonMF/` ownership scope. In particular, the shared completion script
needs a small coordinated repair: it still names `hullHypEmbeddedConeOff` and
`hullSection6Relator`, which are absent from the current assembly.

Final acceptance requires the repaired completion audit, the strict source
scan, a build at the published commit, and closed audits of both unchanged
printed endpoints and the literature/Hull bundles. Keep refutations as
regressions and check that new geometric hypotheses admit the intended models.
There is no defensible completion date until the seed and repaired geometric
interfaces pass the first checkpoint. Those uncertainties are part of the
plan, not work to discover after everything else is finished.
