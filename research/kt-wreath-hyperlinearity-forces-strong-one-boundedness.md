---
rg: 2
id: kt-wreath-hyperlinearity-forces-strong-one-boundedness
kind: claim
title: The q=2 Kun--Thom wreath algebra has 1-bounded entropy at most zero, so any hyperlinear model is entropy-rigid
distinct_from:
  coset-wreath-hyperlinearity-forces-strong-one-boundedness: that is the entropy ceiling for the arithmetic summit wreath W_3; this imports the same ceiling to the Kun--Thom wreath, the group Kun--Thom prove nonsofic, through a different freeness proof.
artifacts:
  - research/artifacts/kt-wreath-double-re-unification-2026-09-11.md
---

**ESTABLISHED.**  For the Kun--Thom Theorem E wreath `W` with `q = 2` (or any
`q` with `gcd(r,q-1) = 1`):

```text
h(L(W)) <= 0 unconditionally;
W hyperlinear  ==>  L(W) strongly 1-bounded, h(L(W)) = 0,
                    delta_0(any generating tuple) <= 1.
```

Microstate spaces of any generating tuple, taken modulo unitary conjugation
(anchored as in Hayes' definition), admit `exp(o(d^2))` epsilon-nets.  So a
hyperlinear model of `W` cannot come in a `c d^2`-parameter family of pairwise
separated non-conjugate completions.

**This ceiling does not refute hyperlinearity, and cannot by itself.**
It is a rigidity constraint on the positive branch, not a sign.
1. It is vacuous off the branch: if `W` is not hyperlinear, then
   `h = -infinity`.
2. The only way to turn it into a refutation is a counting lower bound of
   the form "if `W` is hyperlinear then `h(L(W)) > 0`".  Given this theorem,
   that statement is logically equivalent to non-hyperlinearity of `W`, i.e. a
   restatement rather than a reduction.  The arithmetic lane carries exactly
   such a hole (`coset-wreath-microstates-carry-excess-entropy`), and the same
   hole is deliberately not posed here.
3. The ceiling is symmetric across the equivalence class of
   `kt-wreath-hyperlinear-iff-double-hyperlinear`.  For the double
   `D = G *_Gamma G`, Hayes' join property over the diffuse intersection
   `L(Gamma)`, applied to two copies of the Kazhdan factor `L(G)` (strongly
   1-bounded by property (T), Hayes--Jekel--Kunnawalkam Elayavalli), gives
   `h(L(D)) <= 0` as well.  So entropy carries no information separating the
   two branches of the fork machine.

Its use is as a discipline on constructions: any proposed hyperlinear
architecture for the Kun--Thom wreath must be rigid at the `d^2` scale.

DERIVATION
kt-wreath-strong-one-boundedness-proof
