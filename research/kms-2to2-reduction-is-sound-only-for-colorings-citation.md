---
rg: 2
id: kms-2to2-reduction-is-sound-only-for-colorings-citation
kind: route
title: Import Theorem 1.8 and Remark 1.11 of Khot--Minzer--Safra, On Independent Sets, 2-to-2 Games and Grassmann Graphs (ECCC TR16-124)
target: kms-2to2-reduction-is-sound-only-for-colorings
requires: []
---

Literature import, credited in full.

Subhash Khot, Dor Minzer, Muli Safra, *On Independent Sets, 2-to-2 Games and
Grassmann Graphs*, Electronic Colloquium on Computational Complexity, Report
No. 124 (2016). Conference version: STOC 2017.

Verified from the ECCC PDF, text extracted with pypdf, on 2026-09-18:

* **Page 3.** Conjecture 1.3 (d-to-d Games): "NO case: no coloring satisfies
  more that delta fraction of the constraints of G." The same page defines
  `(j, delta)`-colorings, and page 4 states the variant with that soundness.
* **Pages 4 to 5, Theorem 1.8.** "For every positive integer j and every
  constant delta > 0, for sufficiently small constant eps > 0, there is a
  polynomial time reduction mapping a regular instance (X, Eq) of
  Gap3Lin(1 - eps, s*) to an instance G = (V, E, Phi, Sigma) of Transitive
  2-to-2 Game such that: YES case: ... there is a (1, 1 - delta)-coloring to G.
  NO case: Assuming the combinatorial Hypothesis 2.5, ... there is no
  (j, delta)-coloring to G."
* **Page 5, Remark 1.11**, verbatim: "In an ongoing work with Dinur and Kindler,
  we are investigating whether our reduction, with a slight modification, gives
  soundness in the sense of Conjecture 1.3, i.e., in the NO case, any coloring
  of the 2-to-2 Game instance satisfies only o(1) fraction of its edges. This
  could prove the 2-to-2 Games Conjecture, albeit with imperfect completeness.
  The modification of the reduction amounts to removing some of the constraints
  in the 2-to-2 Game constructed by the reduction."
* **Page 5, Remark 1.12**: "we do not yet have a soundness analysis for the
  reduction."

KMS TR18-006 credits its Grassmann expansion theorem with completing the 2-to-2
theorem (see `two-to-two-games-theorem-citation`). Whether it discharges
Hypothesis 2.5 verbatim is not checked here. Either way, discharging it would
remove the conditional from Theorem 1.8 without changing the kind of soundness
that Theorem 1.8 gives.

Nothing here reproves the theorem.
