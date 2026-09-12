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
