---
rg: 2
id: stw99-problem-lxv-jiang-su-embeddings
kind: claim
title: Characterise the unital algebras admitting a Jiang-Su embedding (STW Problem LXV)
root: true
artifacts:
  - research/artifacts/stw99-structural-cu-cluster-2026-08-30.md
---

**Problem LXV of Schafhauser--Tikuisis--White, arXiv:2506.10902.**
Characterise the unital (simple) C\*-algebras `B` admitting a unital
embedding `Z ↪ B`.  The expected answer (the Dadarlat--Toms
question): `Z` embeds iff `B` has no nonzero finite-dimensional
representations.  Necessity is clear; Dadarlat--Toms proved
sufficiency when `B` unitally contains an infinite-dimensional
subhomogeneous algebra without characters (in particular for
`B ⊗ B'`-type infinite tensor powers).

## Attempts

* `Z = lim Z_{n,n+1}` with semiprojective dimension-drop blocks, so
  the problem reduces to coherent systems of `(n, n+1)`-divisibility;
  by Thiel--Vilalta the no-finite-dimensional-representation
  hypothesis is (2,ω)-divisibility territory and the Global Glimm
  problem (`stw99-problem-lxxiii-global-glimm`) is exactly the
  nilpotent-element engine that would produce the required
  order-zero divisibility at every scale: a positive Global Glimm
  answer supplies, in any unital `B` without finite-dimensional
  representations, full square-zero elements at all scales — the
  standard route from there to `Z_{n,n+1}`-embeddings is
  Robert--Rordam-style division with the obstruction being only
  COHERENCE across `n` (a `lim¹`-type mismatch that semiprojectivity
  reduces to eventually-constant data).  Recorded: LXXIII is the
  load-bearing half of LXV; the residual coherence step is where any
  counterexample must live (a `B` with all finite divisibilities but
  incompatible ones).
