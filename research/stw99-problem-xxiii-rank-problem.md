---
rg: 2
id: stw99-problem-xxiii-rank-problem
kind: claim
title: All ranks occur in unital simple separable stably finite non-elementary C*-algebras (STW Problem XXIII, the Rank Problem)
root: true
artifacts:
  - research/artifacts/stw99-ranks-divisibility-cluster-2026-08-30.md
  - research/artifacts/stw18-23-26-finite-tracial-boundary-audit-2026-08-30.md
---

**Problem XXIII of Schafhauser--Tikuisis--White, arXiv:2506.10902** (the
Rank Problem, first raised in talks of N. Brown, late 2000s).  For `A`
unital simple separable stably finite non-elementary and any lower
semicontinuous affine `f : QT(A) → (0,∞]`, is there a positive
`a ∈ A ⊗ K` with `d_τ(a) = f(τ)` for all quasitraces `τ`?

Known positive cases: stable rank one (Thiel, CMP 2020, Thm 8.11; APRT
Duke Thm 7.14 in the non-simple sr1 case), unique or finitely many
extremal quasitraces, `Z`-stable algebras (ERS Cor 6.8), and strict
comparison + quasitraces-are-traces + compact finite-dimensional
extremal trace boundary (Dadarlat--Toms).

The exact finite-extreme-trace cell is now an explicit established graph
node: `stw23-finite-extreme-trace-boundary-has-all-ranks` imports
Tikuisis--Toms rank surjectivity and uses exactness to identify quasitraces
with traces.  Unlike the stable-rank-one theorem, it assumes neither stable
rank one nor comparison.

## Attempts

* Any counterexample must have stable rank ≥ 2, infinitely many extremal
  quasitraces, and either fail strict comparison or carry a wild trace
  boundary — all known exotic algebras are already covered: Villadsen
  type I has sr1 (EHT) so Thiel applies despite the failure of strict
  comparison; type II has a unique trace.  There is currently no
  candidate on which the problem could fail.
* `stw23-skew-product-diffuse-fibres-have-all-ranks` gives a direct new
  many-trace class.  For a free minimal central dynamical coordinate and a
  unique-trace exact fibre containing one Lebesgue-distributed positive
  contraction, arbitrary affine ranks are lifted to positive orbit averages
  and encoded by spectral cuts.  The invariant-measure simplex can be wild;
  no boundary-dimension hypothesis enters.
* Downstream leverage: all ranks occurring implies all ranks almost
  occurring (continuous affine maps are lsc), and strict comparison plus
  almost-occurrence IS pureness (STW Prop `prop:cu-regular`,
  (7) ⟺ (5)), so this problem implies part (1) of
  `stw99-problem-xxvii-comparison-vs-divisibility`; through the
  `stw99-xxvi-xxvii-imply-xviii` wiring, the Rank Problem plus Winter's
  question XXVI would settle the Toms--Winter conjecture.
* The hard region is a selection problem of the same type as in
  `stw99-problem-xix-uniform-gamma-stably-finite-nuclear`: realizing a
  prescribed rank function fibrewise is easy in each tracial GNS factor;
  making one global element hit it simultaneously across a wild simplex
  is where every partition-of-unity argument needs finite-dimensional
  boundary.
