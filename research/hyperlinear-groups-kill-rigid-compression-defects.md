---
rg: 2
id: hyperlinear-groups-kill-rigid-compression-defects
kind: claim
title: A hyperlinear group containing an infranormal Kazhdan pair has trivial rigid compression defect
distinct_from:
  kt-centralizer-normalization-hs: that is the ultraproduct normalization question for trace-preserving representations of the pair; this is the group-level criterion for arbitrary hyperlinear ambient groups. The two are equivalent by the dichotomy, and the equivalence is recorded by two routes forming a deliberate cycle.
  sofic-groups-kill-rigid-compression-defects: that is the established normalized-Hamming criterion; this is the open normalized-Hilbert--Schmidt criterion, and its failure produces a hyperlinear nonsofic group because the Hamming criterion holds.
  kt-wreath-relative-canonical-actor-exactification: that is one sufficient stability input, actor exactification along canonical wreath microstates; this is the criterion itself, for every hyperlinear group and every rigid pair.
  hs-expander-block-decomposition: that is a structural decomposition input for the Leavitt pair; this is the defect criterion that such inputs would feed.
artifacts:
  - research/artifacts/rigid-compression-defect-ladder-2026-09-11.md
refuted_by:
  - hyperlinear-group-carries-nontrivial-rigid-defect
---

**OPEN, and a win--win.** The claim: for every countable hyperlinear group
`H` and every `Gamma <= G <= H` with `Gamma` and `G` Kazhdan and `Gamma`
infranormal in `G`,

```text
[g z g^-1, gamma] = 1     for all g in G, z in C_H(Gamma), gamma in Gamma.
```

Exactly one of two landmarks follows.

- **If this holds:**
  - the Kun--Thom wreath (`kun-thom-wreath-carries-rigid-defect`) is not
    hyperlinear;
  - so is every free-lamp amalgam `G *_Gamma (Gamma x K)`
    (`weak-mf-groups-can-carry-rigid-defects`);
  - so is the Leavitt configuration, since its commuting factor, Thompson's
    `V`, is nonabelian;
  - so is the torsion-free Fournier--Facio group, whose defect contains its
    simple factor (`fournier-facio-nonhyperlinear-via-rigid-defect`).
    Conversely, a hyperlinear Fournier--Facio group would refute this claim
    (`hyperlinear-rigid-defect-from-fournier-facio`).

  This gives `non-hyperlinear-group`, through the equivalence with
  `kt-centralizer-normalization-hs` and its existing route.
- **If this fails:** some hyperlinear group carries a nontrivial rigid defect
  (`hyperlinear-group-carries-nontrivial-rigid-defect`). By
  `sofic-groups-kill-rigid-compression-defects` it is nonsofic. That gives
  `hyperlinear-nonsofic-group`, so Question 3.4 has a negative answer.

By `rigid-compression-defect-normalization-dichotomy`, this claim is
equivalent to normalization of `sigma(Gamma)' cap prod_U M_n` by `sigma(G)`
for every trace-preserving homomorphism `sigma`, and then for every
homomorphism. That is `kt-centralizer-normalization-hs`.

## Attempts

- **A faithful size on relative commutants.** Property (T) supplies rounding:
  a spectral gap on `L^2(M)` orthogonal to `L^2(M^Gamma)`. Axioms (A1), (A2)
  and (A4) of the conservation criterion hold. It dies at (A3): no faithful
  conjugation-invariant size exists on von Neumann subalgebras of infinite
  index (`invariant-size-collapse`: the trace is refinement-blind). Artifact,
  Section 10.
- **Block decomposition with a compressor clause.** A universal clause dies
  by `nonmonomial-multiplicity-obstructs-hs-compressor-transport`, even for
  exact representations.
- **Exactify the actor restriction.** Models whose restriction to `G` is
  flexibly exactifiable do kill the defect: round `z` into the exact
  finite-dimensional commutant, then apply commutant no-growth. For a single
  compressor this is false
  (`kt-single-compressor-canonical-lamps-do-not-exactify-actor`). The live
  form is multi-compressor exactification,
  `kt-wreath-relative-canonical-actor-exactification`.
- **Transcribe the Hamming proof.** Kun--Thom's size exists only at finite
  stages: vertex masses and isotropy orders of expander components. An HS
  analogue must work at finite matrix levels, with multiplicity coordinates
  rather than in the von Neumann limit. Nothing currently supplies those
  coordinates.
- **Jones basic construction and index (un-tracial-support, 2026-09-13).**
  Dies. `Tr(e_A) = 1` in `<M^ω, e_A>` would force `A = σ(u)Aσ(u)*` only if
  the conjugation were implemented inside `<M^ω, e_A>`. It is
  `σ(u)·Jσ(u)J`, and `Jσ(u)J ∈ (JAJ)'` is exactly the conclusion sought.
  `finite-index-unitary-compression-in-r-omega` gives a strict unitary
  compression in `R^ω` of Jones index 4, so no index read off the position of
  `A` is a size. Artifact `research/artifacts/un-tracial-support-2026-09-13.md`,
  §2 TS2.
- **Spectral gap of `G` alone (un-tracial-support).** Dies. Take any strict
  compressor, with `Γ` and `G` Kazhdan. In `ℓ²(G/Γ)`, `λ(u)δ_Γ` is not fixed
  by `Γ`. So normalization does not follow from unitary representation theory,
  and a proof must use the tracial bimodule structure. Artifact §2 TS1.
- **Calibration against the sofic group `W` (un-tracial-support).**
  - `W` uses `Z^3 ⋊ SL_3(Z)` with `α = Ad diag(2,2,2,1)`: index 8, residually
    finite. Its defect survives in Hilbert–Schmidt norm only because its
    compressor group maps onto `Z`.
  - The Leavitt pair has infinite index, and both `Γ` and `G` are minimally
    almost periodic (`binary-leavitt-unit-group-is-minimally-almost-periodic`).
    So flexible actor exactification cannot reach it.
  - A support for it must use (T) of `G`, both sides of the conjugation
    bimodule, and finite matrix stages, with no genuine representations.
  - Artifact §1, §2 TS4, §3.
- **Packing-profile transcription of the Hamming proof (d-nhg-p5, 2026-09-17, entropy-measure).**
  Dies at the strict-increase step (`wold-multiplicity-blinds-commutant-packing-sizes`).
  - Method: measure the approximate-commutant microstates of `Gamma` and `u Gamma u^-1` by
    2-norm packing counts at a scale `f(d_n)`. Then argue that a nonzero Wold shift `D` makes the
    `B`-count exceed the `A`-count.
  - The counts agree exactly (WH3).
  - At `f = d^2`, every trace-preserving model has identically zero profiles (WH2). The proof
    bounds the averaging operator by `Tr Phi^2 / d^2 -> 2/|W|`.
  - At every other scale, `T_n = Ad sigma_n(u)^-1` averages `K` asymptotically orthogonal
    conjugates of the shift microstates into the commutant microstates. That gives
    `h_A(delta/(sqrt 2 K)) >= K h_D(delta)` (WH1). So the shift is invisible unless `A` already
    has a covering profile of order `1/t`, where orthogonal counting gives no contradiction.
  - Under (T) the shift microstates do contain every bounded element of `D` (WH4). So this is a
    fence on the counting, not on the microstate sets.
  - Escapes: exact per-stage counts (the exactification attempts), and sizes that are not packing
    counts, for example the spectral multiplicities of `Phi`.
