---
rg: 2
id: sv26-bounded-divisibility-dimension-reduction
kind: claim
title: m-comparison, bounded divisibility and a two-piece splitting force purity (Seth--Vilalta)
distinct_from:
  stw99-lxxv-fnd-implies-pure: that is the Antoine--Perera--Thiel--Vilalta dimension reduction starting from finite nuclear dimension; this is the Seth--Vilalta abstract reduction whose inputs are m-comparison, bounded divisibility and a two-piece splitting, with no nuclear dimension assumption.
artifacts:
  - research/artifacts/nucdim-factor-comparison-divisibility-2026-09-16.md
---

Let `D` be a C*-algebra and `m, M in N`.  Assume that `Cu(D)` has
`m`-comparison and that for every `N >= 1` and every `x' << x` in `Cu(D)` there
is `y` with `x' << N y << M x`.  Put `M_1 = 2M^3`.

1. (Reduction and amplification.)  For every `N >= 1` and every `x' << x = [f]`
   in `Cu(D)` there is `c in her(f)_+` with `[c] << x` and
   `x' << N[c] << M_1 x`.
2. (Splitting gives purity.)  If there is `L in N` such that every `x' << x` in
   `Cu(D)` admits `y_0, y_1` with `y_0 + y_1 <= x` and `x' << L y_0, L y_1`, then
   `D` is pure.
3. (Purity gives Glimm.)  If `D` is pure, then `D` has the Global Glimm
   Property.

Here pure means almost unperforated and almost divisible Cuntz semigroup, and
the Global Glimm Property is Kirchberg--Rordam's (for `a in D_+` and `eps > 0`
there is a square-zero `r` in the hereditary subalgebra of `a` whose ideal
contains `(a-eps)_+`).
