---
rg: 2
id: c-linear-sofic-groups-kill-rigid-compression-defects
kind: claim
title: A complex-linear sofic group containing an infranormal Kazhdan pair has trivial rigid compression defect
distinct_from:
  f2-linear-sofic-groups-kill-rigid-compression-defects: that is the normalized-rank row over F_2; this is the row over C. Arzhantseva--Paunescu Question 8.6 asks whether linear soficity passes to a fixed finite field, and no comparison of the two classes is recorded here, so neither row is known to imply the other.
  hyperlinear-groups-kill-rigid-compression-defects: that is the normalized Hilbert--Schmidt row, where property (T) supplies rounding and only a size is missing; this is the rank row over C, where property (T) supplies no rounding.
  sofic-groups-kill-rigid-compression-defects: that is the established Hamming row; this is the row one class up, since sofic groups are linear sofic (Arzhantseva--Paunescu Proposition 4.5).
  rigid-compression-defect-normalization-dichotomy: that is the class-independent equivalence between killing defects and normalizing Kazhdan centralizers; this is the complex-linear instance as a standalone win--win target.
  a-t-menable-groups-have-no-rigid-compression-defect: that shows rigid pairs inside an a-T-menable group are finite with trivial defect in every ambient group, with no approximation hypothesis; this is the open criterion for arbitrary rigid pairs inside complex-linear sofic ambient groups, whose payoff groups contain infinite Kazhdan pairs.
refuted_by:
  - c-linear-sofic-group-carries-nontrivial-rigid-defect
artifacts:
  - research/artifacts/rigid-compression-defect-ladder-2026-09-11.md
  - research/artifacts/weakly-sofic-extension-metric-scope-2026-09-12.md
---

**OPEN, and a win--win.** For every countable group `H` that is linear sofic over `C`,
and every `Gamma <= G <= H` with `Gamma` and `G` Kazhdan and `Gamma` infranormal in `G`,

```text
[g z g^-1, gamma] = 1     for all g in G, z in C_H(Gamma), gamma in Gamma.
```

By [[rigid-compression-defect-normalization-dichotomy]] this is equivalent to
normalization in the rank ultraproduct. For every infranormal Kazhdan pair
`Gamma <= G` and every homomorphism
`sigma : G -> U = prod_omega GL_n(C) / d_rank`, the group `sigma(G)` normalizes
`C_U(sigma(Gamma))`.

## The two payoffs

- **If this holds:**
  - The binary Leavitt unit group is not linear sofic over `C`, since it carries a
    nontrivial rigid defect ([[leavitt-unit-group-carries-nontrivial-rigid-defect]]).
    That gives [[non-linear-sofic-group]] through
    [[non-linear-sofic-via-c-rank-row-defect]].
  - The Kun--Thom wreath is not linear sofic ([[kun-thom-wreath-carries-rigid-defect]]),
    so linear sofic is strictly smaller than weakly sofic.
- **If this fails:** some `C`-linear sofic group carries a nontrivial rigid defect
  ([[c-linear-sofic-group-carries-nontrivial-rigid-defect]]). By the Hamming row it is
  nonsofic, which answers Arzhantseva--Paunescu Question 8.5, "Are all linear sofic
  groups indeed sofic?", negatively, through
  [[linear-sofic-nonsofic-via-c-rank-row-defect]].

Theorem 9 of the ladder artifact records the same dichotomy for the wreath.

## Attempts

- **Transcribing the Hamming proof: dead at both permutation-specific steps.**
  - *(K), rounding into expanding pieces.* Property (T) gives no rank rounding over any
    field, `Q` and `C` included ([[kazhdan-rank-rounding-fails-over-every-field]]).
  - *(T1), one-piece transport.* A compressor can rotate multiplicity coordinates by a
    non-monomial matrix, over any field
    (`research/artifacts/rank-row-compression-audit-2026-09-12.md`, Section 3).
- **A faithful size, axiom (A3) of the ladder's Theorem 10: absent.** Relative commutants
  of images of Kazhdan groups in rank ultraproducts over `C` can be diffuse, with a
  continuous chain of idempotents (part 3 of
  [[kazhdan-rank-rounding-fails-over-every-field]]). So no size comes from atoms.
- **The linear-scale layer: holds over every field, and cannot finish.**
  - [[rank-ultraproduct-compressors-conserve-fixed-right-ideals]] holds over any field.
  - [[linear-scale-rank-conservation-does-not-kill-defects]] shows the layer cannot kill
    defects without property (T) of the compressor group.
- **Cross characteristic for the payoff group.** `L^x` is a group over an
  `F_2`-algebra.
  - Over `C` its root subgroups act by commuting involutions, whose joint eigenspaces
    are canonical, so the (T1) failure mode does not occur for abelian root pieces.
  - The (K) counterexample needs a ring map into a characteristic-zero algebra, which
    `F_2[t]` lacks. So step (K) is open for these models.
  - See Section 5 of
    `research/artifacts/weakly-sofic-extension-metric-scope-2026-09-12.md`.
