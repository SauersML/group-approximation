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
proof dependencies of both endpoints finds exactly the four direct admissions
below; their axiom closures contain the three permitted axioms and `sorryAx`.
The strict source scan independently reports the same four placeholders.
Thus there are no additional admission leaves hidden in the current imported
endpoint proofs, although the proposed reductions below have further unproved
inputs. A successful build does not establish completion.

## All remaining work, including the hidden inputs

| Package | Current assembly admission | What must actually be proved | Completion evidence |
|---|---|---|---|
| Osin diagram construction | `estimatingSelectionConstruction`, line 250 | Construct the reduced O-equivalent diagram, its estimating scaffold, and graph from the source hypotheses | A proved construction at parameters shared with the unbound estimate |
| Osin uncovered boundary estimate | `estimatingUnboundOutput`, line 260 | Replace the false universal-parameter interface by the actual synchronized parameter choice, then prove complementary-region surgery and the arc budget | Closed relative Greendlinger and Hull 4.9 inputs; original refutation retained |
| Hull joint-family preservation | `hullLemma44FamilyInclusionJoint`, line 220 | Greendlinger **plus** a corrected bounded relative-isoperimetric transfer **plus** relator respelling, with one compatible order of constants | Source-faithful bounded family preservation, retaining every conclusion required by the unchanged printed endpoints; preserve the historical unbounded Props explicitly |
| Concrete starting group | `kotowskiOllivier`, line 387 | An actual infinite, finitely presented, torsion-free hyperbolic group with property (T) | Original `Hyperbolic.SharpExistence` passes the closed audit |

The first three packages feed Hull's canonical quotient, one-step construction,
Theorem 7.1, and the common-quotient and Fournier-Facio inputs. The last package
supplies their starting group. Together with the existing Chiodo/Higman and
Minasyan–Osin proofs, these feed `literatureInputs`, `hullInputs`, and both printed
endpoints. All of these consumers must be audited when their inputs close.

## DGO: the complete package is proved

`GGT/DGOProposition414General.lean` proves the **original**
`OsinComponents.DGOProposition414Uniform` at arbitrary `mu ≥ 1`, with one
positive constant chosen before the polygon size, for both the sum and
individual-component conclusions. It also closes the original full
`DGOLemma421b`. Both pass `#audit_closed_axioms` with exactly the three
permitted axioms. The additive API and closed Lemma 4.21(a) remain available.

The general proof uses the completed short isolating-cycle construction to
prove finiteness of the least sum cost. Morse stability selects a uniformly
logarithmic chord using the genuine parameters. The same finite polygon is
exposed to the old combinatorial records with a word-length bookkeeping error,
but that error never chooses a geometric constant or a child radius.
The first and wrapped second arcs, every restricted arc, and every auxiliary
child retain the genuine parameters exactly. Existing isolated-component
families and disjoint factor slots charge witnesses from the general child
costs. An extremal polygon supplies the numerical subdivision inequality;
the proved logarithmic-square overhead and numerical linearity theorem give
the uniform sum bound. Component collapse and recutting give the individual
bound with the same enlarged constant.

The assembly's DGO placeholder has been replaced by that proof. Its DGO
4.14 and 4.21(b) declarations, Hull's finite-avoidance pair producer, and
Hull's full finite-family Corollary 5.7 all pass closed axiom audits.
The assembly build succeeds (10,369 jobs). A fresh traversal of both printed
endpoints finds exactly the four admissions in the table above; the strict
source scan independently reports the same four. The printed endpoints are
unchanged and remain incomplete because those four inputs are still open.

The impossible additive comparison for multiplicative constant greater than
one remains refuted in [#199](https://github.com/SauersML/group-approximation/issues/199).
The completed general proof does not use that premise.

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

The graph audit found two further proved obstructions. The historical
`InteriorIncidencePlanarRealization` cannot represent an isolated cell in a
dart-only map ([#203](https://github.com/SauersML/group-approximation/issues/203)).
More seriously, `HasHereditaryPlanarEdgeBound` uses one-endpoint coverage and
is equivalent to **no incidences**, so `EstimatingGraphData` forces its
interior-edge type to be empty
([#204](https://github.com/SauersML/group-approximation/issues/204)).
`HereditaryPlanarRefutation.lean` proves both defects, including a concrete
closed refutation of the realization. `EndpointClosedDeletion.lean` restores
the all-endpoints invariant, proves its preservation under deletion and the
five-deletion-order consequence, and verifies a nonempty one-edge model.
These are checked repairs of the finite graph input, not a completed Osin
construction. Next migrate the graph/data/weighted consumers to that invariant
and prove the actual selected graph geometry, treating isolated vertices and
tree components explicitly. Preserve the old records and refutations.
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
work. The relative-area induction already exists, but its historical transfer
is **false**, not merely unfinished. Issue
[#201](https://github.com/SauersML/group-approximation/issues/201) now has a
closed Lean refutation: the quotient F₂ → ℤ², with all quotient-null basis
words as relators, has the requested area bound and finite peripheral support
while its image Cayley graph fails every four-point bound. The counterexample
also satisfies admissibility and the kernel equation.

The source check found that `IsLemma44Input.stronglyBounded` omits the published
uniform bound on relator lengths. `HullSCLemma44BoundedInput` now preserves that
historical definition, adds `IsBoundedLemma44Input`, and proves that the actual
auxiliary one-relator producer supplies it. Its explicit
`BoundedRelativeLinearAreaTransferStatement` remains to be proved, and the
bounded condition must be migrated through the family and quotient consumers.
This is a source-hypothesis repair; the printed Theorem E endpoints stay fixed.
`HullSCLemma44BoundedFilling` carries this condition through the existing
area induction and ball-injectivity proof to the actual bounded filling
conclusion, conditional on Greendlinger and the corrected bounded transfer.
It uses neither of the refuted transfer/pullback interfaces.

The original-ball pullback certificate is also too strong, even for a bounded
filling of C₂ * C₂; see
[#202](https://github.com/SauersML/group-approximation/issues/202). Source
relative balls can all be `{1}`, while a new quotient base edge reaches a
nonidentity peripheral element. Properness can still hold. The corrected
transfer therefore concludes quotient hyperbolic embeddedness directly.
Its proof should use finite peripheral support where needed, allowing the
source metric to be enlarged by that finite support. A standalone Lean proof
of the bounded C₂ * C₂ pullback counterexample remains pending.

For respelling, `HullSCLemma44JointRelabel` proves a joint transport only under
additional alphabet/base-containment conditions. The original-family
respelling is still an input, and those conditions must be derived in the
actual construction. Audit this proposed intermediate statement against the
source before extending its proof chain. If it is too strong, report the
counterexample and use a justified direct joint-diagram argument while retaining
the full required preservation conclusions and explicitly accounting for the
published boundedness hypothesis.

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

General DGO geometry is now closed. Next close the synchronized Osin
construction and its Greendlinger/Hull 4.9 consumers, Hull 4.4's remaining
controls, the concrete seed, and the final assembly. These have distinct proof
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
