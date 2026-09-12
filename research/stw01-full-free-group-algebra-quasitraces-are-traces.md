---
rg: 2
id: stw01-full-free-group-algebra-quasitraces-are-traces
kind: claim
title: The full free group algebra C*(F_2) carries only linear 2-quasitraces
distinct_from:
  stw99-problem-i-quasitraces-are-traces: that is Kaplansky's question for every C*-algebra; this is one fixed universal instance, the full group C*-algebra of F_2, to which the whole question reduces.
  stw01-kaplansky-iff-free-group-qt-invariance: that is a tensor test over the reduced algebra C*_r(F_2) quantified over all unital A; this is linearity on the single non-exact full algebra C*(F_2).
  stw01-matrix-product-algebras-have-qt-linearity: that proves linearity on products of matrix algebras and their quotients; this asks for linearity on a residually finite-dimensional subalgebra of such a product, where quasitraces need not extend.
artifacts:
  - research/artifacts/stw01-certificates-products-universal-tests-2026-09-11.md
  - research/artifacts/stw01-host-survey-2026-09-12.md
---

Every bounded 2-quasitrace on the full group C*-algebra `C*(F_2)` is a trace.

**Why this is the right open target.** By Theorem 3.1 of
`research/artifacts/stw01-certificates-products-universal-tests-2026-09-11.md`,
this statement is equivalent to STW Problem I. The implication into the root is
`stw01-problem-i-via-full-free-group-host`. The same proof gives three further
equivalent forms, recorded in `research/artifacts/stw01-host-survey-2026-09-12.md`:

1. every bounded 2-quasitrace on `C*(Gamma)` is a trace, for one (equivalently
   every) countable group `Gamma` that surjects onto `F_2`;
2. every bounded 2-quasitrace on the universal unital C*-algebra of two positive
   contractions, `C([0,1]) * C([0,1])`, is a trace;
3. every bounded 2-quasitrace on every unital residually finite-dimensional
   C*-algebra is a trace (`C*(F_2)` is RFD, Choi 1980).

The reduced algebra `C*_r(F_2)` is exact, so Haagerup's theorem already covers
it. The universal test sits on the full, non-exact side.

## Attempts

- **Exactness (Haagerup).** Dead: `C*(F_2)` is not exact (Wassermann 1976), and
  every counterexample host is non-exact.
- **One-sided inequalities** (Dixmier averaging, Jensen for the pinching by
  `diag(1,-1)`). Dead: Proposition 4.1 of the universal-tests artifact shows that
  one-sided additivity on `A_+` already forces linearity, so such an inequality is
  the problem itself.
- **Certificate counting and Haagerup–Thorbjørnsen descent.** Dead (artifact §8):
  the counting constants satisfy `C_N >= 1`, and the descent needs exactness of
  the host.
- **RFD envelope.** `C*(F_2)` sits inside `prod_k M_(n_k)`, on which every bounded
  2-quasitrace is a trace (`stw01-matrix-product-algebras-have-qt-linearity`).
  Dead as a reduction: quasitraces do not extend from subalgebras in general, and
  extension to the product would make the quasitrace a trace outright. That is a
  restatement, not a step.
- **Repo non-exact hosts.** The Kun–Thom nonsofic groups are exact, so their
  reduced algebras are excluded (`stw01-kun-thom-reduced-group-algebras-are-qt-linear`).
  Their full group C*-algebras are non-exact but have finite abelianization, so
  they admit no surjection onto `F_2` and are not universal tests. The binary
  Leavitt unit group is simple, hence has no free quotient either, and its
  exactness is not recorded in Cairn. No mechanism for a non-additive quasitrace
  on any of these hosts is known.
- **AW*-side.** The statement is equivalent to W*-ness of every type `II_1`
  AW*-factor (`stw01-quasitrace-crux-is-awstar-factor-w-star`).
  Arulseelan–Hanson normality gives nothing at the factor level. The problem splits
  into monotone completeness plus exclusion of wild `II_1` factors
  (`stw01-problem-i-via-monotone-complete-ii1-factors`).
