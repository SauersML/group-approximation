---
rg: 2
id: measurable-alphabet-compression-over-leavitt-units
kind: claim
title: The uniform Bernoulli shift over the Leavitt units has an almost-everywhere injective equivariant code into fewer symbols
distinct_from:
  leavitt-units-have-zero-rokhlin-entropy-supremum: that is zero Rokhlin entropy for every free action; this is a concrete coding object that implies it by counting one partition, and the converse goes only through Seward's generator theorem, which is not imported.
  leavitt-unit-group-nonsurjunctive: that asks for a continuous injective non-surjective automaton on one full shift; this allows any Borel code, injective only almost everywhere, into a strictly smaller alphabet.
artifacts:
  - research/artifacts/measurable-alphabet-compression-2026-09-12.md
---

**OPEN.** Let `U = L_(F_2)(1,2)^x`. There are finite alphabets `A, B` with `|B| < |A|` and a
Borel map `tau: A^U -> B^U`, commuting with the shift, that is injective on a set of full uniform
product measure.

Such a `tau` gives the generating partition `{tau(x)(1) = b}` with `|B|` pieces. So the uniform
Bernoulli shift over `U` has Rokhlin entropy at most `log |B| < log |A|` (Section 1 of the
artifact), and `leavitt-zero-supremum-via-measurable-compression` turns that into the zero Rokhlin
entropy supremum. Conversely a deficit gives such a code after amplifying the alphabet, through
Seward's Krieger generator theorem (arXiv:1405.3604). That direction is a remark only, since the
statement has not been read from the source here.

This is the "decoder correct almost everywhere" form of the measurable negative target: the decoder
is the Borel inverse of `tau` on its image.

## Attempts

- **Routing codes.** Dead: `measurable-certificate-routing-preserves-bernoulli-measure`. A code
  that keeps a certificate and fills each output data site from one input data site is a
  measure-preserving bijection almost everywhere, even with Borel routing of unbounded displacement.
  Mass transport over the group is the obstruction; the end-fixing tree shows it is essential.
- **Hilbert-hotel coset compressions.** Dead:
  `bernoulli-factors-to-infinite-stabilizer-coset-shifts-trivial`. Borel factors of the free
  Bernoulli shift into coset shifts with infinite stabilizers are constant. So the strict coset
  embedding of `compressed-coset-shifts-carry-strict-equivariant-embeddings` cannot be pulled onto
  the free shift, even measurably.
- **Linear codes.** A nonzero linear functional of uniform iid symbols is uniform, so a code must
  be nonlinear.
- **Localization.** Good finite approximations of `tau` are deficit configurations.
  `sofic-radical-localizes-bernoulli-deficit-witnesses` makes their points generate a nonsofic
  subgroup, so the code must use a nonsoficity configuration of `U`.
- **What remains.** A synergistic code: one output symbol recording a nonlinear function of input
  symbols along a compressor `u Gamma u^-1 < Gamma`, decodable because `Gamma` has no invariant
  observables. No construction is known. Section 4 of the artifact.
- **Homomorphic and linear codes.** Dead: `homomorphic-codes-cannot-compress-bernoulli-shifts`.
  A code that is a group homomorphism, or linear or affine over a finite field, kills a nonzero
  constant and so collides everywhere. Combining many symbols linearly does not help.
- **Continuous codes and pre-injectivity.** A continuous code injective almost everywhere is
  pre-injective (Section 6 of the artifact). Pre-injectivity is not enough: Bartholdi–Kielak
  (J. Eur. Math. Soc. 2019; a literature remark, not imported) give pre-injective non-surjective
  automata over every nonamenable group, sofic ones included. So the target is strictly between
  pre-injectivity and injectivity.
- **Ascent.** Compressions over a subgroup induce compressions over the whole group through left
  cosets (Section 6). A compression over Thompson's `V` would give one over `U`, and would prove `V`
  nonsofic.
- **Compressor codes (2026-09-12).** The minimal ansatz is a nonlinear `f` on a window
  `W_0 ∪ t W_0`, with `W_0` in a Kazhdan `Gamma` and `t Gamma t^-1 < Gamma` strict. Where it dies
  (Section 7 of the artifact):
  - `bernoulli-codes-descend-to-window-subgroup` reduces it to the subgroup the window generates.
  - `Gamma`-invariant observables are constant, and strictness lives only on `U/Gamma`, which
    Theorems A and B keep out of reach.
  - `strict-kazhdan-compression-gives-no-bernoulli-deficit`: the Kun--Thom actor carries a strict
    Kazhdan compression and is Rokhlin-maximal, so the saving cannot come from compression plus (T).
  - The code must use a relation failing in that actor, such as the rigid defect. The test case is
    whether a Kun--Thom LEF-lamp wreath (surjunctive, nonsofic, with nontrivial defects) is
    Rokhlin-maximal. That is open.
- **Defect coupling through routing (2026-09-12, w3-measurable).** Dead in its factorized form:
  `single-maximal-stage-routed-codes-cannot-compress`. A code `R_2 o S o R_1` with Borel routing
  `R_1`, an alphabet-preserving `R_2`, and one combining stage `S` whose window generates a sofic
  subgroup never compresses, however far the routing moves symbols along the nonamenable actor. So
  the rigid defect cannot be coupled to the actor by "combine locally, then transport". The combining
  window must itself generate a nonsofic subgroup, and synergy spread over two or more combining
  stages is outside the theorem. Designing a code is exactly designing a generating partition with
  fewer pieces (`compression-codes-are-small-generating-partitions`). Closedness measured in the
  ambient profinite topology of `U` filters nothing, since every proper subgroup is non-closed
  (`profinite-localization-is-vacuous-over-leavitt-units`). The witness-level filters still bite:
  closedness in the profinite topology of the subgroup a witness generates, and nonsoficity of that
  subgroup. Artifact:
  `research/artifacts/defect-coupled-routed-codes-2026-09-12.md`.
