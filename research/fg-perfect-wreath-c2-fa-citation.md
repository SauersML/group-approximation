---
rg: 2
id: fg-perfect-wreath-c2-fa-citation
kind: route
title: Import the Cornulier--Kar criterion for property FA of standard wreath products and specialize to B = C_2
target: fg-perfect-wreath-c2-has-property-fa
requires: []
artifacts:
  - research/artifacts/fg-perfect-wreath-c2-fa-citation-2026-09-17.md
---

This is a citation import. It restores the demoted attempt artifact
`research/artifacts/fg-perfect-wreath-c2-fa-citation-2026-09-17.md` after an
independent referee pass (2026-09-17, agent swarm-0917-w5-bh-wreath-fa).

Y. Cornulier and A. Kar, *On Property (FA) for wreath products*, J. Group Theory
14(1) (2011) 165--174; arXiv:1004.2582. The abstract was re-read verbatim from
arxiv.org/abs/1004.2582 on 2026-09-17:

> "We characterize permutational wreath products with Property (FA). For
> instance, the standard wreath product A wr B of two nontrivial countable groups
> A,B, has Property (FA) if and only if B has Property (FA) and A is a finitely
> generated group with finite abelianisation."

**Specialization.** Let `A` be finitely generated and perfect, and `B = C_2`.
- If `A = 1`, then `W = C_2` is finite. Every finite group has a bounded orbit on
  any tree, so it fixes a vertex or an edge, hence a vertex, since the action is
  without inversions.
- If `A != 1`, both `A` and `C_2` are nontrivial and countable, since finitely
  generated groups are countable. `C_2` has FA by the previous item. `A` is
  finitely generated with trivial, hence finite, abelianisation. The standard
  wreath product `A wr C_2` is `(A x A) ⋊ C_2` with the swap, which is `W`. By
  the quoted criterion, `W` has FA.

**Referee checks.**
- *Hypotheses.* "Standard wreath product" in the abstract is the restricted
  wreath product over the regular action of `B`. For finite `B` restricted and
  unrestricted agree, so there is no ambiguity.
- *Calibration.* For `A = Z`, which has infinite abelianisation, the criterion
  predicts failure. Indeed `(m, n, e) -> m + n` maps `Z wr C_2` onto `Z`, which
  acts on a line without a fixed point. For `A = Z/2` the criterion predicts FA,
  and `Z/2 wr C_2` is the dihedral group of order 8, which is finite. The
  import therefore agrees with both calibration inputs. `∎`
