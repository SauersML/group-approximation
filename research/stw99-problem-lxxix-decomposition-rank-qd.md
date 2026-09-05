---
rg: 2
id: stw99-problem-lxxix-decomposition-rank-qd
kind: claim
title: Characterise finite decomposition rank by quasidiagonality conditions for nowhere scattered algebras (STW Problem LXXIX)
root: true
artifacts:
  - research/artifacts/stw99-final-band-cluster-2026-08-30.md
  - research/artifacts/stw79-index-dichotomy-2026-09-04.md
---

**Problem LXXIX of Schafhauser--Tikuisis--White, arXiv:2506.10902.**
For nowhere scattered `A` with finitely many ideals and finite nuclear
dimension, characterise finite decomposition rank in terms of
quasidiagonality-type conditions.

The unrestricted characterization remains open in this graph. The
2026-09-04 check of arXiv v2 still finds it stated as Problem LXXIX.

There is an exact positive answer for essential extensions by stable simple
unital AF algebras whose K-zero group is totally ordered.
`stw79-total-order-af-index-dr-dichotomy` proves that, when the simple
unital nuclear UCT quotient has torsion-free K-zero and finite
decomposition rank `d`, the middle algebra has rank
`d` precisely when its index boundary vanishes, and infinite rank
otherwise. In that class, finite decomposition rank, strong
quasidiagonality, quasidiagonality and stable finiteness are equivalent.
All members have exactly three ideals, are nowhere scattered, and have
finite nuclear dimension. This is a consequence of published theorems,
not a claimed new solution of the general problem.

## Attempts

* **Composition factors alone fail.** The previous proposal to test
  strong quasidiagonality on simple factors of an ideal filtration is
  refuted by `stw79-same-factors-different-decomposition-rank`. Two
  essential extensions with identical UHF-stable compact ideal,
  irrational-rotation quotient, ideal chain and singleton tracial state
  space have decomposition ranks one and infinity. Their index maps
  differ. This is not a counterexample to testing all subquotients,
  including the middle algebra itself.
* **Projectional gluing succeeds under a proved hypothesis.** A
  quasicentral approximate unit of projections gives the classical
  decomposition-rank maximum. Schochet's relative-quasidiagonality
  theorem supplies exactly that hypothesis in the zero-index class
  above. This does not prove a corresponding statement for arbitrary
  nowhere scattered ideals or arbitrary quotient K-theory.
* **The remaining step is extension-sensitive.** The former equality
  slogan relating this problem to LXXXII and strong-QD bookkeeping was
  not a proved reduction and is withdrawn. Neither finite nuclear
  dimension of a simple quotient nor its quasidiagonality is being
  asserted here to imply finite decomposition rank without the required
  tracial hypotheses. The full LXXIX characterization still needs to
  handle those hypotheses and extension data beyond this AF-ideal case.
