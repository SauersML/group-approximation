# Final review and resolution report for `non_mf_groups_exist.tex`

Date: 2026-08-14

## Verdict

The load-bearing mathematics was re-derived from the manuscript and checked
against the Lean declarations.  No unresolved contradiction or false step is
known in the proved non-MF theorem, the Clifford witness, the Kazhdan transport
argument, the finite-dimensional shadow, the finite-normal criterion, or the
group-C-star consequences.

The revision now presents one short conceptual spine:

> Kazhdan transport makes the compression defect tracially invisible, while
> the Clifford model makes its square the nontrivial central sign.

The formal claims have an intentionally strict boundary.  Every manuscript
Lean badge resolves to one declaration whose theorem header is source-level
closed; no property-(T), construction, soficity, MF, or literature premise is
accepted from the caller.  Literature-only consequences are left unbadged.

## Mathematical and expository defects resolved

- The main result is now motivated from the MF question and the
  Blackadar--Kirchberg context before technical machinery appears.
- The beautiful ultraproduct transport/sign proof is the main route to
  non-MF; finite-stage Reynolds averaging is presented as the stronger general
  layer rather than as a second conceptual proof of the same fact.
- The finite presentation, its exact relator count, the rank-at-most-six
  reduction, the witness map, and the nontriviality of the marked involution
  are separated cleanly.
- The formerly implicit identity `d w d^{-1}=w^{-1}` now has one labeled
  display and is reused wherever redundancy of the involution relator is
  invoked.
- The cyclic calibration has a real proof environment and states precisely
  what exact finite-dimensional invisibility does and does not imply.
- Terminology for corona representations, detection, asymptotic
  representations, and normalized Hilbert--Schmidt convergence occurs before
  first use.
- The universe-relative maximal group algebra notation no longer creates an
  illegal double subscript and its role is disclosed.
- The MF radical, portability, universal MF quotient, Horn obstruction,
  clopen marked-group cylinder, positive MF controls, quotient failure, and
  extension failure are ordered as consequences of the main mechanism.
- The paper now states the sofic-to-hyperlinear consequence and asks the
  converse question without pretending that operator-norm models supply a
  trace.
- The finite-normal method's torsion obstruction is stated exactly: a finite
  subgroup of a torsion-free group is trivial.
- The bibliography now includes and accurately describes the August 2026
  Fournier--Facio and Kun--Thom developments, while making explicit that the
  OpenAI and Kun--Thom papers are contextual rather than logical inputs.
- Anonymous output no longer exposes the repository owner through badge
  links.  The public mode links each badge to the reviewed formal source.
- A compact formal-verification paragraph explains exactly what a tag certifies
  and that the formal property-(T) route uses a rational spectral certificate,
  not the literature proof used by the human manuscript.

## Load-bearing mathematical checks

The review treated the following as failure points rather than routine
background.

- **Literal base and property (T).**  The displayed base relators are the
  relators used by the formal presentation.  The formal proof reaches the
  literal group through a rational spectral certificate with gap at least
  `1/500`; the human proof still states a standard literature route, so the
  certification is supplementary rather than a hidden premise.
- **Compression algebra.**  The relators imply the one-sided compression
  identities used in transport, and the commutator calculation gives
  `dwd^{-1}=w^{-1}` and `u^2=w`.  The proof never silently replaces
  normalized Hilbert--Schmidt convergence by operator-norm convergence.
- **Kazhdan transport.**  The integrated action in the finite norm
  ultraproduct is an honest unitary representation; the Kazhdan projection
  identifies its fixed space; and one-sided compression preserves that fixed
  space.  This is precisely what makes `u` tracially invisible.
- **Final sign contradiction.**  In the Clifford witness the central sign is
  genuinely nontrivial and is represented by `-1`, so `u^2=w` cannot converge
  both to `1` in normalized Hilbert--Schmidt norm and remain the scalar
  `-1`.
- **Finite-dimensional shadow.**  Exact unitary representations kill the
  marked element, but the text does not infer residual finiteness or MF from
  that fact.  The cyclic calibration explicitly displays the gap between
  exact finite-dimensional invisibility and the operator-norm conclusion.
- **Reduced group C-star passage.**  Only the valid direction is used: an MF
  embedding of `C*_r(G)` restricts to a faithful corona representation of
  the canonical group unitaries.  No converse is asserted.
- **Stable finiteness.**  Faithfulness of the canonical reduced trace is
  proved, its matrix amplification is faithful, and the trace of the defect
  projection turns an isometry into a unitary in every finite amplification.
- **Exactness.**  The locally finite lamp kernel is amenable/exact, the
  quotient is a linear subgroup of `GL_4(Q)` and hence exact, extension
  permanence gives exactness of the witness, and discrete group exactness
  gives exactness of its reduced group algebra.  This literature-dependent
  chain is stated openly and receives no Lean badge.
- **Soficity.**  Successive telescope levels are commensurable with the base,
  and the whole vertical group commensurates the base; orbit--stabilizer
  therefore makes every level orbit on the coset site set finite.  Finite
  Clifford windows then lie in finite level-invariant lamp subgroups.  Local
  finite-kernel permanence, semidirect-product reassociation, and the split
  integer-extension theorem prove the concrete witness sofic without an
  auxiliary model or an identification step.
- **Radical scope.**  What is proved is `w`-membership and functorial
  portability.  Exact computation of the radical is never inferred from
  membership alone.

No gap was found in these checked implications.  The unresolved strengthening
problems below require new mathematics and are not disguised as consequences
of compactness, finite-dimensional representation theory, or standard
permanence results.

## Design and readability decisions

The shortest robust presentation is not the shortest possible sequence of
symbols.  It is the shortest route that lets a reader verify each change of
category.  The revised order is therefore:

1. state the MF convention and the compression mechanism;
2. prove abstract Kazhdan transport;
3. isolate the central-sign criterion;
4. give the literal presentation and Clifford witness;
5. derive the radical, marked-group, permanence, sofic/hyperlinear, and
   C-star consequences;
6. end with the precise operator-norm boundary and open questions.

This keeps the conceptual proof short while moving relator verification,
equivalence bookkeeping, and formal certification away from the narrative
spine.  Repeating the transport argument at finite stages would be longer and
less memorable; suppressing the category changes would be shorter but unsafe.

## New closed Lean mathematics

The release-facing collection is
`GroupApproximation/Endpoint/NonMFImpact.lean`.  In addition to the literal
non-MF theorem it now contains premise-free endpoints for:

- the six-generator finitely presented non-MF group;
- the nonempty clopen cylinder consisting of non-MF marked groups;
- the full scaling family for every integer factor at least two;
- the concrete locally finite/LEF/sofic/MF lamp kernel and the finitely
  generated non-MF witness;
- the concrete finitely generated witness being simultaneously sofic and
  non-MF;
- the same concrete witness being hyperlinear and non-MF;
- residual finiteness, soficity, and MF of the affine base through explicit
  congruence quotients;
- a concrete MF group with a non-MF quotient;
- one dimension-independent finite test set and positive defect threshold
  forcing the marked word within operator norm `< 1` of the identity;
- the precise torsion-free limitation of the finite-normal obstruction;
- the general implication `sofic and non-MF => hyperlinear and non-MF`;
- a separable reduced group C-star algebra of the concrete witness with its
  faithful canonical trace, stable finiteness in every finite matrix
  amplification, and failure of MF.

The last two witness items strengthen the algebraic endpoint from the
presented group `E` to the concrete Clifford witness `W` without introducing
a theorem input.  The premise-free theorem
`NonMFImpact.witness_sofic_nonMF` now certifies the headline separation.

The reusable supporting theorems separate the argument cleanly.
`MappingTelescopeFiniteOrbits.lean` proves the finite site-orbit calculation;
`FiniteOrbitInvariantKernel.lean` turns those orbits into finite invariant
Clifford subgroups without choosing lamp normal forms; and
`SoficMarkedCompression.lean` combines them with the local finite-kernel and
integer-extension permanence theorems.  These modules are necessarily
quantified, but the concrete manuscript endpoint discharges every input.

## Exactness upgrade

The manuscript now proves that `C*_r(W)` is exact as well as separable,
faithfully tracial, stably finite, and non-MF.  The proof uses three standard
published results transparently: linear groups are exact; exact groups are
closed under extensions; and for discrete groups, group exactness is
equivalent to exactness of the reduced group C-star algebra.  The kernel is
locally finite and the quotient is the displayed subgroup of `GL_4(Q)`.

Exactness itself is deliberately not marked as Lean-verified.  The imported
mathlib surface has no definition of exact C-star algebras or exact groups, so
a purported closed exactness theorem would currently be either a facade or a
new foundational formalization.  All other assertions in that paragraph are
covered by the new closed witness-C-star endpoint.

## What remains genuinely open

These are not manuscript defects that can be repaired by wording, and the
paper does not claim them.

1. **Exact MF radical.**  The equality
   `Rad_MF(E) = {1,w}` reduces to proving `E / <w>` is MF.  Existing
   Hilbert--Schmidt convergence does not give the operator-norm separation
   required for that quotient; the compression defect can survive on small
   corners.  No proof is presently known.  There is a concrete intermediate
   test: every exact finite-dimensional representation kills
   `u = [tct^{-1},v_1]`, whereas `u` survives algebraically in the commuting
   lamp quotient `W/<zeta>`.  Proving that target MF would show that `u` is not
   in the MF radical, but it still would not prove that all of `E/<w>` is MF.
   Such models would have to be genuinely non-finite-quotient in flavor:
   Theorem B already rules out residual finiteness as a route for detecting
   the surviving image of `u`.
2. **Effective quantitative modulus.**  Compactness gives a finite set and a
   positive, dimension-independent defect threshold.  It does not compute a
   numerical threshold on the displayed relators from the `1/500` rational
   spectral gap.  An effective modulus remains valuable new work.
3. **Soficity and structure of `E`.**  The kernel of `E -> W`, a normal form,
   the word problem, and soficity of the finitely presented group `E` remain
   unresolved.
4. **Multiplicity results.**  Pairwise non-isomorphism of the scaling family
   and continuum-many isomorphism types in the clopen cylinder are not proved.
5. **Broader targets.**  Extending transport from matrix coronas to arbitrary
   norm ultraproducts of finite traced C-star algebras is plausible but needs
   a precisely chosen target category and a new proof.
6. **MF versus hyperlinearity in the paper's convention.**  For the weak CDE
   norm-corona definition, operator-norm multiplicativity controls the
   Hilbert--Schmidt defect but does not supply faithful coordinate traces.
   The manuscript therefore asks whether MF implies hyperlinearity and
   distinguishes this from stronger trace-controlled notions also called MF.

## Cairn research frontier

The manuscript's research state is represented in the repository's Cairn
graph, not only in prose.  Proof artifacts remain in the manuscript, Lean
modules, and review documents; Cairn names the reusable propositions and the
valid implications between them.  The migrated graph records the complete
conceptual spine from Kazhdan transport through the central-sign and
Kazhdan--Clifford criteria to the literal non-MF mark.  It also records the
scaling family, finite-normal criterion, universal MF quotient, radical
functoriality, finite Horn obstruction, clopen cylinder, positive MF controls,
quotient and extension failures, the sofic/hyperlinear non-MF witness, the
two reduced-group-C-star consequences, the simple sofic envelope, and the
cyclic-base sharpness example.

Open questions are first-class roots rather than prose afterthoughts.  In
particular:

- `literal-mark-quotient-mf` is the unique open prerequisite on the displayed
  route to `literal-mf-radical-exact`;
- `commuting-lamp-quotient-mf` is the remaining prerequisite on the route to
  `unsquared-defect-mf-visible`, alongside the established survival proof;
- `literal-witness-kernel-amenable` gives a concrete live route to soficity of
  the finitely presented source `E`; and
- the effective modulus, torsion-free example, MF-to-hyperlinear direction,
  multiplicity questions, broader tracial targets, and comparison with the
  known nonsofic constructions are explicit frontier roots.

Cairn's duplicate check is clean.  The compiled graph has 96 claims and 93
routes: 61 claims are established, 14 routes are invalidated by proved
obstructions, and 27 frontier holes remain.  The graph now names both the
commensurated-level orbit theorem and its direct proof route.  This prevents, among other
mistakes, treating radical membership as an exact radical calculation,
confusing the established sofic quotient `W` with the unresolved soficity of
`E`, or trying to detect the unsquared defect by residual finiteness.

## Submission actions outside the repository

- Archive the release and cite its DOI; a repository edit cannot mint that
  external identifier.
- Replace the public `verified` branch links by the immutable archived commit
  once the release object exists.
- Record the pinned dependency `mathlib v4.32.2` and the axiom-audit result in
  the release notes.  The audited endpoint surface uses no project literature
  axioms; only Lean's standard classical primitives occur where expected.
- Repeat the priority/literature sweep immediately before submission because
  the nonsofic and MF literature is moving on a scale of days in August 2026.

## Verification gates

The following were run on MSI only, using shared warm caches and no CI or
local compilation:

- all 43 manuscript Lean references resolve;
- all 43 cited declarations have closed theorem headers;
- all 35 numbered theorem-like claims match the exact-claim manifest and its
  declaration roster;
- the Cairn graph compiles with 96 claims and 93 routes, its changed-file
  duplicate/lint check is clean, and its static site generator completes;
- the changed non-MF release, public, and axiom-audit Lean targets build with
  warnings as errors;
- LuaLaTeX/`latexmk` completes with no undefined citations or references and
  no overfull or underfull boxes.

A separate aggregate-root probe was deliberately capped at 32 GiB; Slurm
stopped it for exceeding that memory allocation after replaying 3384 of 3579
targets, without a Lean error.  It is not counted as a successful full-root
build and was not retried by consuming an excessive share of a shared node.

The source audit and the claim manifest are separate on purpose: the first
prevents hidden theorem inputs, while the second detects printed-statement
drift, missing badges, stale dependencies, and mismatched declaration links.
