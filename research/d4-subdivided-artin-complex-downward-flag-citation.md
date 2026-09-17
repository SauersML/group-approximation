---
rg: 2
id: d4-subdivided-artin-complex-downward-flag-citation
kind: route
title: Import Huang's bowtie freeness and downward flagness of the subdivided D_4 Artin complex
target: d4-subdivided-artin-complex-downward-flag
requires: []
---

Citation import, not a reproof. Read on 2026-09-17 from the arXiv LaTeX source of J. Huang,
*Cycles in spherical Deligne complexes and application to K(π,1)-conjecture for Artin groups*,
arXiv:2405.12068, Theorem `thm:downflagD4`, verbatim: "Suppose Λ is the Coxeter diagram of
type D_4, and take two leaf nodes a and b from Λ. The (a,b)-subdivision of Δ_Λ with its
vertex set endowed with the order introduced in Definition [def:subdivision], is a bowtie free
and downward flag poset."

The subdivision is Definition `def:subdivision` of the same paper, applied to the `B̃_3`-shaped
diagram `D_4` with `(b_1, b_2) = (a, b)`, `b_3 = d` (the centre) and `b_4 = c`. In Huang's proof,
bowtie freeness is checked with Lemma `lem:bowtie free criterion`. Downward flagness is quoted
from J. Huang, *Labeled four cycles and the K(π,1)-conjecture for Artin groups* (D_n paper,
"huang2024Dn"), Corollary 7.7. That primary source was not read.

The partial order property is Lemma `lem:poset` of arXiv:2405.12068. It needs the subdiagram to
be admissible, and here it is the whole diagram.
