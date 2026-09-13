---
rg: 2
id: rf-higman-embedding-for-decidable-groups-fails-citation
kind: route
title: Import Theorem 1 of Rauzy, arXiv:2002.02540
target: rf-higman-embedding-for-decidable-groups-fails
requires: []
---

**Source.** E. Rauzy, *Obstruction to a Higman embedding theorem for residually finite groups with solvable word problem*.
- arXiv:2002.02540v2, 17 Mar 2021; J. Group Theory (2021), DOI 10.1515/jgth-2020-0030.
- Read from the arXiv LaTeX source (`HigmanObstruction.tex`) on MSI, 2026-09-13.

**Numbering.** The source declares `\newtheorem{thm}{\protect\theoremname}` with one global counter (facts, propositions and lemmas share it), and the introduction is `\section*{Introduction}`, unnumbered. So the first theorem prints as Theorem 1. The labels `fact:3` and `fact:4` on the next two numbered statements agree. The journal numbering was not checked.

**The theorem.** The sentence immediately before it:

> "It was unknown whether the condition of having solvable word problem is sufficient for such embeddings to exist. For instance, in the article [Kharlampovich2017], the authors ask whether ``unsolvability of the word problem is the only obstacle'' to embed recursively presented residually finite groups into finitely presented residually finite groups. We answer negatively to that question:"

> **Theorem 1.** "There exists a finitely generated residually finite group with solvable word problem, that does not embed in any finitely presented residually finite group."

[Kharlampovich2017] is Kharlampovich--Myasnikov--Sapir, *Algorithmically complex residually finite groups*, arXiv:1204.6506 (Bull. Math. Sci. 7 (2017)). Its §1.1.7 is the source of `rf-higman-embedding-for-decidable-groups`.

**Proof structure** (same source, verbatim).
- Theorem 2: "There exists a finitely generated residually finite group with solvable word problem, that is not effectively residually finite."
- "Theorem 1 then follows from the following facts:"
  - Fact 3: "A finitely presented residually finite group is effectively residually finite."
  - Fact 4: "A finitely generated subgroup of an effectively residually finite group is itself effectively residually finite."

**Match with the target.** Theorem 1 is exactly the statement of `rf-higman-embedding-for-decidable-groups-fails`.
