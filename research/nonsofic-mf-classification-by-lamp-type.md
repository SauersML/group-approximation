---
rg: 2
id: nonsofic-mf-classification-by-lamp-type
kind: route
title: Classify the compression-mechanism nonsofic groups by lamp type
target: nonsofic-mechanism-mf-classification
requires: [symmetric-double-weak-mf, kun-thom-clifford-extension-not-weak-mf, kun-thom-wreath-weak-mf]
artifacts:
  - notes/WEAK_MF_NONSOFIC_DOUBLE.md
  - notes/FALSE_CLIFFORD_NORM_MF_STERILITY.md
  - notes/PERFECT_CORE_KUN_THOM_WREATH.md
  - notes/NOTEPAD.md
  - research/artifacts/radical-renormalization-2026-08-23.md
---

# Classify the compression-mechanism nonsofic groups by lamp type

The classification question asks which of the known one-sided-compression
nonsofic groups are MF, in order to separate the shared group-theoretic input
from the metric-specific Hamming and operator-norm obstructions. The corpus now
answers all three lamp types, and the answers split by **lamp type**, not by the
compression pattern — precisely the separation the target claim asks for.

## The three lamp types over one Kazhdan pair

Fix a residually finite nonnormal infranormal Kazhdan pair `Gamma < G` with a
strict compressor, `X = G/Gamma`. The mechanism produces three groups over the
same `X`, differing only in what sits on the lamps.

**Free lamps — weak MF (settled, positive).** `symmetric-double-weak-mf`:
`D = G *_Gamma G` and the finite-lamp family `G *_Gamma (Gamma x K)` are weak
MF, by Fell absorption of the regular representation plus Shulman's C-star
amalgam theorem. With `kun-thom-nonsofic-wreath` these are explicit **weak MF
and nonsofic** groups.

**Clifford lamps — not weak MF (settled, negative).**
`kun-thom-clifford-extension-not-weak-mf`: every homomorphism from the complete
or sparse Clifford extension to a norm matrix corona kills the central sign
`z`. The same holds for the perfect even cover
(`notes/PERFECT_CORE_KUN_THOM_WREATH.md`, Proposition 8).

**Commuting lamps — not weak MF (settled, negative).**
`kun-thom-wreath-weak-mf` is closed directly by pointwise torsion collapse. A
strict compressor makes the nontrivial lamp at `s Gamma` fixed by
`s Gamma s^-1`, while its `Gamma`-orbit consists of commuting involutions.
Every norm-matrix-corona representation therefore identifies two distinct
coordinate lamps, so it kills a nontrivial two-lamp word.

## What the split shows

The completed three-row classification answers the target claim outright. The
compression mechanism is **not** what decides MF: the same pair `Gamma < G`,
the same compressor, and the same nonsoficity mechanism produce both a weak-MF
example and non-weak-MF examples. Free lamps survive by the
amalgam/Fell-absorption mechanism, whereas commuting torsion already collapses
under the compressor and Clifford lamps have the stronger central-sign
obstruction. The shared Kazhdan/compression geometry controls nonsoficity; the
lamp relations decide the operator-norm MF verdict.

## Two entries deliberately excluded

- **The Leavitt unit group** `EL_4(L_(F_2)(1,2))` and its Steinberg cover.
  Their weak MF status is open (`notes/NOTEPAD.md:770-777`, with a failed
  Fock/leaf finite-section attempt recorded at `:818-828`), so they cannot
  enter a classification whose rows are weak-MF verdicts. Their nonsoficity
  is no longer the obstacle: `openai-leavitt-unit-nonsofic` is established,
  and `universal-leavitt-el4-nonsofic` proves it here for `EL_4` outright.
- **The reduced group C-star algebra** `C_r^*(G *_Gamma G)`. MF-ness of the
  algebra is a strictly stronger and separately open question
  (`notes/UNIQUE_TRACE_KUN_THOM_DOUBLE.md:166-176`), and the standard warning
  applies: `C^*(F_infty)` is residually finite-dimensional, hence MF, while its
  QWEP status is Kirchberg's conjecture, false after the negative solution of
  Connes embedding. Group-level weak MF and algebra-level MF must not be
  conflated. The split form now supplies a sharper boundary:
  `finite-dimensional-nielsen-cocycle-models-kill-mark` proves that **every
  exact finite-dimensional equivariant quantum model** of the free radical
  kills the marked free generator. Thus Gao--Kunnawalkam Elayavalli--Mj's
  ambient-strong-convergence upgrade cannot start from exact actions here;
  any reduced-MF proof must construct genuinely asymptotic actions already at
  the finite stages.
