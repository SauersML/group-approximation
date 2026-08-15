# Four formalization directives: scaffold inventory and designs

Date: 2026-08-15.  User-ordered targets, each mapped against what is
already kernel-checked and what remains, ranked by tractability.

## 1. Strict Kazhdan compression makes `C*_max` infinite / not stably finite

**Status: most tractable — algebraic engine complete, instantiation
missing.**  In-repo, done: `Analysis/ProperIsometryFromCompression.lean`
(`ProperProjectionCompression` data ⟹ explicit isometry `s = p u* + (1-q)`
with `s*s = 1 ≠ ss*`, not Dedekind-finite, not stably finite, no faithful
tracial state, no injective hom to a Dedekind-finite ring);
`Analysis/UniversalKazhdanCStarConsequences.lean` (transport along
injective star embeddings; the reduced algebra admits NO proper
compression); `Analysis/MaximalGroupCStar.lean` (universe-relative
`C*_max` with generators, unitaries, evaluation against arbitrary
`CStarUnitaryRepresentation`s); `Kazhdan/KazhdanProjection.lean`
(per-representation average operators, invariant projections, and the
uniform norm bound `norm_averageOperator_pow_sub_projection_le` with
constants depending only on the Kazhdan pair).

**Remaining bricks:**
* (b1) the Kazhdan projection as an element of `MaximalGroupCStar G`:
  componentwise `invariantProjection` over the representation family,
  with membership in the closed subalgebra from the uniform convergence
  of the average powers (the Kazhdan-pair constant is
  representation-independent — this is the whole point);
* (b2) the absorption identities `p q = p = q p` for `q = u p u*` with
  `u` the stable-letter unitary — componentwise from
  `Fix(Λ) ⊆ Fix(tΛt⁻¹)` in every representation;
* (b3) properness `q ≠ p` from STRICT compression: one witnessing
  component, the quasi-regular representation on `ℓ²(G/K)` for
  `K = t ι(Λ) t⁻¹`: the delta at the base coset is `K`-fixed, and any
  `a ∈ ι(Λ) \ K` moves it.  Needs a permutation-unitary representation
  on `lp 2` of a countable coset space (check the repo's ℓ² permutation
  machinery before building).
Assemble into `ProperProjectionCompression (MaximalGroupCStar G)` and
every conclusion drops out of the existing theorems.

**Sizing update (same day):** Mathlib has GNS
(`Analysis/CStarAlgebra/GelfandNaimarkSegal.lean`: per-state Hilbert
space + `gnsStarAlgHom`) but NOT the assembled Gelfand--Naimark
embedding.  Hence (b1)'s componentwise spectral gap over *abstract*
C*-components is the irreducible analytic brick, with route: for a
self-adjoint contraction `h` and spectral value in the gap region,
produce a state via the commutative `C*(h) ≅ C(sp h)` and positive
Hahn--Banach extension, take its GNS representation, realify (a
complex-unitary representation is a real-orthogonal one with the same
operator norms and the same fixed subspace), and contradict the
in-repo real Kazhdan machinery
(`Kazhdan/KazhdanProjection.norm_averageOperator_pow_sub_projection_le`).
Sub-bricks: state extension (check Mathlib), the realification bridge,
and the gap-transfer.  The purely algebraic β-bricks (the averaging
element of `MaximalGroupCStar`, its self-adjointness, the conjugation
identity, and the `ℓ²(G/K)` strictness witness) are independent of β2
and can land first.

## 2. Torsion-free finitely presented non-MF with full MF radical

**Status: analytic half and consequence package fully kernel-checked;
group-theoretic witness is the open program.**  Done:
`normalKazhdan_le_normMFResidual` and the collapse/saturation layer;
`TorsionFreeFullMFRadical` + `TorsionFreeFullMFConsequences` +
`TorsionFreeFullMFCStarConsequences` derive the entire endpoint package
(torsion-free, f.p., `Rad_MF = ⊤`, every nontrivial quotient non-MF,
reduced-algebra consequences) from `DefectRoutingData`; the paper proof
of the witness is written and adversarially audited
(`docs/TORSION_FREE_NORMAL_GENERATION_HULL_QUOTIENT.md`, verdict
CONFIRMED).

**Remaining: construct `DefectRoutingData`.**  This is acylindrical
small cancellation.  Two architectures:
* FF-literal: universal f.p. torsion-free group (Higman), f.p. simple
  torsion-free group (Burger–Mozes/Hyde–Lodha), torsion-free hyperbolic
  (T) group (random groups), double HNN, Hull 7.1 twice.  Every input is
  a major formalization; none exists in Mathlib (no hyperbolic groups at
  all).
* Cost-collapsed variant worth designing first: replace the random-group
  (T) input by an EXPLICIT `C'(1/6)` presentation whose property (T) is
  certified by the repo's exact SOS/Hodge pipeline (the P13 machinery is
  reusable); classical `C'(1/6)` metric small cancellation
  (hyperbolicity, torsion-freeness via Greendlinger) is combinatorial
  and much lighter than the acylindrical theory.  The common-quotient
  step (Hull/Osin) remains the irreducible core; its formalization is a
  Bass–Serre-free normal-form program over relative presentations.
This is a months-scale lane; the `DefectRoutingData` boundary was
externally endorsed and stays the certification interface until the
program lands.

## 3. Undecidability of MF recognition for finite presentations

**Status: reduction framework complete; Adian–Rabin construction
missing.**  Done: `Computability/MarkovMFConsequences.lean` (Markov
witness data + presentation-code semantics + the operator-MF recognition
predicate; computable/RE pullbacks) and
`Computability/CStarRecognitionConsequences.lean`
(`reducedCStarMF_recognition_undecidable`,
`maximalCStarMF_recognition_undecidable`,
`maximalCStar_finite_recognition_undecidable` — all conditional on an
`AdianRabin`-transformation input).  The Markov witnesses themselves are
unconditional in-repo: the trivial group is MF; the literal `E` is
finitely presented non-MF.

**Remaining: the Adian–Rabin transformation** — a computable map of
presentation codes with the pointwise correctness theorem.  Content:
free products with amalgamation/HNN with Britton's lemma over coded
presentations, plus computability of the code manipulations.  Bounded
but large; entirely combinatorial (no analysis).  Suggested first brick:
Britton's lemma for HNN extensions of presented groups over Mathlib's
`PresentedGroup`, stated code-level.

## 4. Multiplicity / 2-generator consequences

**Status: paper proofs recorded; Lean not started.**
* Continuum multiplicity: `research/continuum-nonisomorphic-fg-non-mf-proof.md`
  — `E × N_S` for B.H. Neumann's continuum family `N_S`; pairwise
  non-isomorphism recovers `S`; non-MF passes up from the `E` factor
  (`IsOperatorMF.subgroup` contrapositive, in-repo).  Bricks: the
  Neumann family (finitely generated, continuum-many, pairwise
  non-isomorphic — elementary but sizable combinatorics of alternating
  groups), and the product/subgroup plumbing (exists).
* 2-generator: a 2-generated non-MF group via a Higman–Neumann–Neumann
  embedding of `E` into a 2-generator group plus subgroup permanence.
  Requires an HNN/amalgam embedding theorem with Britton normal form —
  shares its core brick with directive 3.  (Six-generated is already
  kernel-checked: `LiteralSixGenerator`.)

## Execution order

(1) → this session (bricks b1–b3);  (4)-continuum and (3)/(4)-Britton
share a combinatorial program;  (2) is the long lane behind the endorsed
routing boundary.  Directives 3 and 4 share Britton's lemma — build it
once.
