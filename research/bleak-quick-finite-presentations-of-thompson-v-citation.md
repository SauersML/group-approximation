---
rg: 2
id: bleak-quick-finite-presentations-of-thompson-v-citation
kind: route
title: Import Bleak--Quick Theorems 1.3 and 2.1 and equation (2.4) from the TeX source
target: bleak-quick-finite-presentations-of-thompson-v
requires: []
artifacts:
  - experiments/thompson-v-models/presentation_bq2.json
  - research/artifacts/thompson-steinberg-presentation-2026-09-12.md
---

C. Bleak and M. Quick, *The infinite simple group V of Richard J. Thompson: presentations by
permutations*, Groups Geom. Dyn. 11 (2017) 1401-1436; arXiv:1511.02123v2.

Checked 2026-09-12 by lane `ex-free-objects` against the arXiv e-print
(`PresentationForV-FinalVersion.tex`, fetched on MSI) and the PDF text (ghostscript `txtwrite`).
- Theorem 1.2: "R. Thompson's group V has a finite presentation with three generators (00 01),
  (01 10 11) and (1 00) and eight relations R1-R5".
- Theorem 2.1 (`thm:mainWithWords`): "R. Thompson's group V has a finite presentation with three
  generators a, b and c and the following eight relations", equation (2.3) (`eq:R-words`).
- The paragraph after it: "the normal closure, in the free group on {a,b,c}, of the following
  eight relations is identical to that of our original list", equation (2.4) (`eq:KB-words`).
- Theorem 1.3 (`thm:2gen-KB`): "R. Thompson's group V has a finite presentation with two
  generators u and v and the seven relators".
- Conventions (Section 2): maps act on the right, `t_(alpha,beta)` swaps prefixes, and
  `t^s = s^-1 t s`. By (2.5), `(00 01) = a`, and `b` induces the 3-cycle `(01 10 11)`.

The Theorem 1.3 relators were copied from the same TeX by lane `nh-thompson-v` into
`experiments/thompson-v-models/presentation_bq2.json` and checked there on binary strings. The
(2.3) and (2.4) words were transcribed verbatim into
`experiments/nonsofic-certificates/presentations/verify_thompson_steinberg_presentation.py`. There
all sixteen words hold exactly in `L_(F_2)(1,2)^x` under `g -> U_g^-1`, which is a necessary check
on the transcription. What is imported is only that these lists present `V`; the proofs are
Bleak--Quick's, and (2.4) and Theorem 1.3 rest on their reported KBMAG reductions.
