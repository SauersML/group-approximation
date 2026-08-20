---
rg: 2
id: uniform-halting-pauli-word-oracle
kind: claim
title: A finite presentation exposes the post-halting Pauli question oracle with constant average defect
distinct_from:
  dimension-reported-pauli-test-halting-compiler: that states the final machine-to-group semantics in terms of a valid nonlocal strategy; this is the remaining syntactic group-word oracle before the exact maximally-entangled extraction.
  adaptive-all-pairs-schur-replica-table-compiler: that must emit a complete finite multiplication table after inspecting residual dimension internally; this emits only the BLR and Magic-Square question oracle after receiving dimension as a machine output.
---

Construct effectively from a source machine `M` a finite presentation,
marked word, and positive computable source-dependent defect modulus
satisfying `(IMK1)`, such that if `M` halts and outputs `D`, the presentation
exposes the question-indexed binary
observables and constant-answer PVMs of the Pauli braiding test at an `N`
satisfying `(PBD2)`.  Every `D`-dimensional marked tuple of sufficiently small
presentation defect must make the verifier's **average** rejection probability
at most `eta_0` after independent fixed-size PVM rounding at each sampled
question.

The conversion must use only finitely many group-word templates. Its average
defect bound and mark retention may depend computably on the source code but
must be independent of `N`, `D`, and the runtime before the output. A
nonhalting computation must retain an exact marked model, so the oracle
hardware is dormant rather than inconsistent.

## Attempts

- Naming all `2^N` linearity questions after the halt is not a finite
  presentation compiler; quantitative Higman embedding makes their derivation
  cost depend on runtime.
- Encoding questions by a tape action is sufficient only if uniformly random
  BLR triples and Magic-Square contexts are conjugates of finitely many local
  templates.  Raw shift/wreath encodings lose representative coherence.
- Dinur powering gives constant classical constraint density and the Pauli
  braiding test gives constant quantum rigidity.  The missing splice is a
  perfect-complete self-similar orbit presentation realizing their query
  sampler in arbitrary unitary normalized-HS microstates.
