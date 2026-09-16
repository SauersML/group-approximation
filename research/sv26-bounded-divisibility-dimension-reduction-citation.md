---
rg: 2
id: sv26-bounded-divisibility-dimension-reduction-citation
kind: route
title: Import Seth--Vilalta Lemma 5.4 and Theorem 5.6, re-deriving the splitting induction
target: sv26-bounded-divisibility-dimension-reduction
requires: []
artifacts:
  - research/artifacts/nucdim-factor-comparison-divisibility-2026-09-16.md
---

**Established by citation, with partial re-derivation.**  Source:
Seth--Vilalta, *Continuous functions over a pure C*-algebra*,
arXiv:2602.14809v2 (v1 16 Feb 2026, preprint), source file `CXA_pure.tex`,
statements checked against the source on 2026-09-16.

1. Item 1 is SV Lemma 5.4 (`prp:RedandAmp`).  Its proof uses the Cuntz
   semigroup axioms O6 and O7 through the elementary SV Lemmas 5.2 and 5.3, and
   the cut-down into the hereditary subalgebra uses SV Lemma 2.3(i), i.e.
   Kirchberg--Rordam, Amer. J. Math. 122 (2000), Prop. 2.7.  The constants were
   re-checked (artifact Section 7).
2. Item 2 is SV Theorem 5.6 (`prp:Gen_DimRed`), (ii) implies (iii).  Artifact
   Section 7 re-derives the induction giving `m+1` pieces `y_0, ..., y_m` with
   `sum_j y_j <= x` and `x' << L^m y_j`, and the chain showing that `D` is
   `n`-almost divisible for `n = 2 L^m M_1` (for `k >= 1` and `x' << x`, item 1
   with `N = 2kL^mM_1` gives `z'` with `kz' <=_s y_j` for all `j`, so
   `kz' <= x` by `m`-comparison, and `x' << (k+1)(n+1)z'`).  The remaining
   import is Antoine--Perera--Thiel--Vilalta, *Pure C*-algebras*,
   arXiv:2406.11052v3, Theorem 5.7 (`prp:PureMain`): `(m,n)`-pure algebras
   are pure.
3. Item 3 is SV Theorem 5.6, (iii) implies (i): almost divisibility with `N = 2`
   gives `(2,omega)`-divisibility, which is equivalent to the Global Glimm
   Property by Thiel--Vilalta, arXiv:2204.13059, Theorem 3.6 (as quoted in SV
   Paragraph 5.5).

Trust surface: two preprint imports (APTV Theorem 5.7; SV Lemma 5.4, whose
proof was re-checked) and one import from Thiel--Vilalta for item 3 only.
