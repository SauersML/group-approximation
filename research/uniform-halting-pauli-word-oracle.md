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
- The exact machine-addressing subproblem has a concrete model:
  `msz-clifford-machine-skeleton-has-polynomial-fillings` exposes one
  computation-indexed Pauli pair in a finitely presented involution group and
  gives polynomial fillings for its commutator phase.  This does not expose
  the verifier's random linearity questions or turn polynomial pointwise cost
  into the constant average bound required here, but future constructions can
  reuse the skeleton instead of rebuilding a Turing HNN tape.
- Encoding questions by a tape action is sufficient only if uniformly random
  BLR triples and Magic-Square contexts are conjugates of finitely many local
  templates.  Raw shift/wreath encodings lose representative coherence.
- Dinur powering gives constant classical constraint density and the Pauli
  braiding test gives constant quantum rigidity.  The missing splice is a
  perfect-complete self-similar orbit presentation realizing their query
  sampler in arbitrary unitary normalized-HS microstates.
- `generator-column-pauli-test-globalizes-but-does-not-pin-sites` shows that
  the analytic verifier is already strong enough when its questions are the
  generator-matrix columns of an asymptotically good `[K,n,d]` code:
  `K=Theta(n)` gives `O(log n)` sampling and dimension-independent global
  Pauli exactification.  What it does not give is this node's word oracle.
  Explicit polynomial-time column generation is not bounded relator area,
  and the global correcting isometry can mix all sites with the multiplicity
  reservoir unless the computation incidence is compiled at the same time.
- `lin-introspection-payload-is-global-gauge-covariant` removes the global-
  frame ambiguity as a separate analytic obstacle: Lin transports every
  `Read/Hide/Sample/Intro` PVM through the same Pauli extraction isometry.
  But the verifier's classical dense-column parity calculation is not an
  ordinary group word.  Thus this node is now the exact remaining gate for
  that source-specific route, rather than site-noise localization or an
  additional anchor packet.
