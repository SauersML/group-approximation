---
rg: 2
id: self-twisted-bt-group-fp-embedding-iff-solvable-wp-citation
kind: route
title: Import BBMZ Corollary 4.14 and Higman's embedding theorem, with the brick algorithm written out
target: self-twisted-bt-group-fp-embedding-iff-solvable-wp
requires: []
artifacts:
  - research/artifacts/zp-z3-08-twisted-bt-artin-2026-09-13.md
---

This is a citation import, checked by a written proof. All quotations come from
Belk–Bleak–Matucci–Zaremsky, *Progress around the Boone–Higman Conjecture*,
arXiv:2306.16356, ar5iv rendering, read 2026-09-13:

- **Theorem 4.13:** "If G is a finitely generated group then G·V_G is a finitely
  generated simple group, and G embeds isometrically into G·V_G." Here G acts on
  itself by translation.
- **Corollary 4.14:** "A finitely generated group G has solvable word problem if and
  only if the group G·V_G is computably presented." This is (2)⇔(4).
- **Step (3)⇔(4)** is stated in the survey as "It is easy to see that G·V_G has
  solvable word problem if and only if G does."
- **Higman's embedding theorem,** as stated there: "Let G be a finitely generated
  group. Then G is computably presented if and only if G embeds into a finitely
  presented group." This is (1)⇔(2).

The artifact §3 writes out the steps the survey leaves to the reader:
- the brick algorithm for (4)⇒(3), with a proof that twists are unique on nonempty
  open sets;
- Kuznetsov's two enumerations for (2)⇒(3), using simplicity from Belk–Zaremsky,
  arXiv:2001.04579, Theorem 3.4.

**Trust surface.**
- The survey was read through an HTML rendering by a summarizing fetch tool, and a
  fetch of the arXiv v3 HTML timed out, so the numbers 4.13 and 4.14 are those of the
  ar5iv rendering.
- The primary papers of Higman (1961) and Kuznetsov (1958) were not re-read.
- Belk–Zaremsky Theorem A (finite generation) and Theorem 3.4 (simplicity) are
  consumed as stated.
