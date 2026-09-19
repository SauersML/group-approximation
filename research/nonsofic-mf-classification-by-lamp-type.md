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
---

# Classify the compression-mechanism nonsofic groups by lamp type

The classification question asks which of the known one-sided-compression
nonsofic groups are MF, in order to separate the shared group-theoretic input
from the metric-specific Hamming and operator-norm obstructions. The corpus
already answers it for two of the three lamp types, and the answers split by
**lamp type**, not by the compression pattern — which is precisely the
separation the target claim is after.

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

**Commuting lamps — open.** `kun-thom-wreath-weak-mf`, the middle case, is the
one remaining leaf. It is not decided by either neighbour: the Clifford result
above lives on the sign `z` that is killed in passing to `W`, and the free-lamp
argument consumes an amalgam decomposition that `W` does not have.

## What the split already shows

The two settled entries answer the qualitative part of the target claim
without waiting for the third. The compression mechanism is **not** what
decides MF: the same pair `Gamma < G`, the same compressor, and the same
nonsoficity proof yield a weak MF group with free lamps and a non-weak-MF group
with Clifford lamps. So the operator-norm obstruction is not a shadow of the
Hamming one — it is carried entirely by the lamp algebra, specifically by
whether there is a central sign for the Kazhdan projection argument to cut a
corner on.

That is a complete answer to "separate the shared group-theoretic input from
the metric-specific obstruction" in the qualitative sense. The route is
nevertheless not complete until the commuting-lamp case is decided, because the
target asks for a determination of each known example, and `W` is the original
Kun--Thom example.

## Two entries deliberately excluded

- **The Leavitt unit group** `EL_4(L_(F_2)(1,2))` and its Steinberg cover.
  Their weak MF status is open (`notes/NOTEPAD.md:770-777`, with a failed
  Fock/leaf finite-section attempt recorded at `:818-828`), so they cannot
  enter a classification whose rows are weak-MF verdicts.  Their nonsoficity
  is no longer the obstacle: `openai-leavitt-unit-nonsofic` is established,
  and `universal-leavitt-el4-nonsofic` proves it here for `EL_4` outright.
- **The reduced group C-star algebra** `C_r^*(G *_Gamma G)`. MF-ness of the
  algebra is a strictly stronger and separately open question
  (`notes/UNIQUE_TRACE_KUN_THOM_DOUBLE.md:166-176`), and the standard warning
  applies: `C^*(F_infty)` is residually finite-dimensional, hence MF, while its
  QWEP status is Kirchberg's conjecture, false after the negative solution of
  Connes embedding. Group-level weak MF and algebra-level MF must not be
  conflated.
