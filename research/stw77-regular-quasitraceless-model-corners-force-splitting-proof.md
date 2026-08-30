---
rg: 2
id: stw77-regular-quasitraceless-model-corners-force-splitting-proof
kind: route
title: Turn trace-invisible regular corners into proper supports and split the model commutant
target: stw77-regular-quasitraceless-model-corners-force-splitting
requires:
  - stw77-fd-commutant-splitting-iff-proper-supports
  - stw77-proper-support-models-force-oinfty-stability
---

Fix a model `D` as in the claim and a chosen minimal support `p_j`.  Put
`C_j=p_j B p_j`, a simple unital C*-algebra with unit `p_j`.  The
almost-unperforated simple dichotomy, in the quasitracial form recorded in
Fu--Lin, [Proposition
4.9](https://doi.org/10.1017/fms.2021.79), says that if `C_j` is not purely
infinite, then it is stably finite and admits a nonzero `2`-quasitrace.  In
the unital case this quasitrace can be normalized.  The model hypothesis
excludes that alternative.  Hence `C_j` is purely infinite, and its unit
`p_j` is properly infinite in `C_j`, therefore also in `B`.

This holds for one minimal projection in every simple summand of `D`.
`stw77-fd-commutant-splitting-iff-proper-supports` therefore supplies two
isometries with orthogonal ranges in `B intersect D'`.  Since such models are
available for every finite packet and tolerance,
`stw77-proper-support-models-force-oinfty-stability` makes the inclusion
`E->B` `O_infinity`-stable.

If `B` is exact, every corner `C_j` is exact.  Haagerup's theorem identifies
its normalized `2`-quasitraces with its tracial states, proving the stated
replacement.  Finally, `Z`-stability makes `W(C_j)` almost unperforated by
Rordam, [Theorem 4.5](https://arxiv.org/abs/math/0408020), giving the last
sufficient condition.
