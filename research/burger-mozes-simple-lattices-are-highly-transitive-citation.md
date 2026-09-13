---
rg: 2
id: burger-mozes-simple-lattices-are-highly-transitive-citation
kind: route
title: Import BFFHZ Remark 3.5 on the Burger--Mozes groups
target: burger-mozes-simple-lattices-are-highly-transitive
requires: []
---

Citation import. J. Belk, F. Fournier-Facio, J. Hyde, M. C. B. Zaremsky,
*Boone--Higman embeddings of Aut(F_n) and mapping class groups of punctured
surfaces*, arXiv:2503.21882v2, Remark 3.5. Read from the extracted PDF text on
MSI (`/scratch.global/sauer354/bh-reviewer/2503.21882.txt`, l.745--760) on
2026-09-13; the verbatim passage is in the target.

**The argument's chain, as BFFHZ give it:**
1. Density of `Λ` in a boundary-2-transitive closed subgroup of `Aut(T)`
   [BM97, Remark 5] makes `Λ ↷ ∂T` extremely proximal.
2. By [FLMMS22, Theorem B], topological freeness of `Λ ↷ ∂T` suffices for high
   transitivity.
3. If topological freeness failed, extreme proximality would give three
   pairwise disjoint translates of an open set carrying a nontrivial rigid
   stabilizer. That yields a direct product of three nontrivial groups in `Λ`,
   which cohomological dimension 2 forbids.
4. For finitely generated simple groups, highly transitive implies MIF [HO16,
   Theorem 5.9], [LBMB22b, Proposition A.1], and Theorem C (iii) gives PBH.

BFFHZ also cite [BLIW] for PBH of these groups by a different method.

Not reproved here; no Lean counterpart.
