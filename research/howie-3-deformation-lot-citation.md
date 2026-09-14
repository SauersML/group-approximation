---
rg: 2
id: howie-3-deformation-lot-citation
kind: route
title: Import Howie's 1983 theorem that one-cell complements of point-deformable 2-complexes 3-deform to LOT complexes, pinned from two secondary sources
target: howie-point-deformable-complex-minus-cell-deforms-to-lot
requires: []
artifacts:
  - research/artifacts/ideas-bridges-2-2026-09-14.md
---

**Source.** J. Howie, *Some remarks on a problem of J. H. C. Whitehead*, Topology 22
(1983), no. 4, 475--485, doi:10.1016/0040-9383(83)90038-1.

**Primary not read.** On 2026-09-14 ScienceDirect refused the web tool with HTTP
403. It returned a bot-check HTML page, not the PDF, to curl on MSI, both with and
without a cookie jar. Before review this import must be re-checked against the
printed paper. Needed: the exact numbered statement, and whether `L` is assumed
finite.

**Secondary pin 1, verbatim.** M. A. Cerdeiro, *A class of locally indicable LOT
groups* (preprint PDF, cms.dm.uba.ar/Members/manuelacerdeiro), p. 2:
- "Howie had proved in [How83] that if a 2-complex L can be 3-deformed to a point,
  and e is a 2-cell of L, then the subcomplex K = L − e can be 3-deformed to a LOT
  complex. A consequence of this fact is that if the Andrews-Curtis conjecture were
  true, then the asphericity of LOT complexes would imply the compact case of the
  Whitehead conjecture. Recall that the Andrews-Curtis conjecture asserts that every
  contractible 2-complex can be 3-deformed to a point (see [AC65])."
- Bibliography, p. 9: "[How83] ______, Some remarks on a problem of J.H.C.
  Whitehead, Topology 22 (1983), no. 4, 475–485." The blank stands for J. Howie,
  the author of the preceding entry [How82].
- Same p. 2, on the companion paper [How85] = J. Howie, *On the asphericity of
  ribbon disc complements*, Trans. Amer. Math. Soc. 289 (1985), no. 1, 281--302:
  "Howie showed in [How85] that LOT complexes are 2-dimensional spines of ribbon
  disc complements."

**Secondary pin 2, verbatim.** M. A. Cerdeiro, E. G. Minian, *A new approach to
Whitehead's asphericity question*, arXiv:1203.5348v1, p. 1:
- "In 1983 J. Howie [7] reduced the problem to the following two particular cases."
- "Theorem 1.1 (Howie). If the answer to Whitehead's question is negative, then
  there exists a counterexample K ⊂ L of one of the following two types: (a) L is
  finite and contractible, K = L − e for some 2-cell e of L, and K is non-aspherical.
  (b) L is the union of an infinite chain of finite non-aspherical subcomplexes
  K = K_0 ⊂ K_1 ⊂ ⋯ such that each inclusion map K_i → K_{i+1} is nullhomotopic."
- "Howie proved that if the Andrews-Curtis conjecture and the ribbon disc
  complements conjecture are true, then there are no counterexamples of type (a)."
- Bibliography, p. 9: "[7] J. Howie, Some remarks on a problem of J. H. C.
  Whitehead. Topology 22 (1983). 475-485."

**Match.** The target is the first sentence of pin 1. Pin 2 confirms the
consequence for type (a) counterexamples and the reference. Both pins come from the
same research group, so they are not fully independent confirmations of the
wording.

**How it is used.** `balanced-kervaire-stable-ac-lot-proof` applies the target to
a finite contractible presentation complex whose presentation is stably AC-trivial.
The (AC1)--(AC5) moves are realized by 3-deformations, sketched in that route, so
the complex 3-deforms to a point. It is finite, so finiteness of `L` is not an
issue there.
