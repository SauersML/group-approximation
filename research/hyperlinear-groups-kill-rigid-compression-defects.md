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
