---
rg: 2
id: sl3z-cocompact-quotient-uniquely-ergodic-minimal
kind: claim
title: SL3(Z) acting on SL3(R)/Λ with Λ cocompact is minimal and uniquely ergodic
artifacts:
  - research/artifacts/sl3z-cocompact-quotient-microstates-2026-09-13.md
distinct_from:
  sl3z-on-cocompact-lattice-quotient-is-not-sofic: that is the open soficity question for this action; this records the topological rigidity of the same action, which makes that question independent of the measure
---

**ESTABLISHED.** Let `Λ <= SL_3(R)` be a cocompact lattice. For the left action of `SL_3(Z)` on the
compact space `SL_3(R)/Λ`:

1. every orbit is infinite;
2. every orbit is dense;
3. the Haar probability measure is the only invariant Borel probability measure.

*Why.* `SL_3(Z)` is Zariski dense. A finite orbit of `gΛ` would put a conjugate of a unipotent
`u_12(n)` into `Λ`, and a cocompact lattice has no nontrivial unipotent elements. An invariant measure
with an atom would have a finite orbit. So Benoist--Quint Corollaire 1.2(a), (b) give 3 and 2
(`benoist-quint-zariski-dense-invariant-measures-are-haar`).

The same holds for any Zariski-dense subgroup of `SL_3(R)` containing a nontrivial unipotent element.

Proof in `sl3z-cocompact-quotient-uniquely-ergodic-minimal-proof`.
