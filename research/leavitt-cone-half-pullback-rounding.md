---
rg: 2
id: leavitt-cone-half-pullback-rounding
kind: claim
title: Pullbacks of asymptotic representations of St_20 of the binary Leavitt algebra along the path-algebra surjection round flexibly on the Kazhdan cone half
distinct_from:
  leavitt-st20-nonhyperlinear-iff-cone-bound-and-half-rounding: that asks (HR), rounding of restrictions σ_n|Delta_+ along the inclusion, and needs (QC) as well; this asks rounding of pullbacks σ_n∘φ_* along the surjection φ_*, and needs nothing else.
  el-r-polynomial-vertex-not-flexibly-hs-stable: that asks for a non-roundable asymptotic representation of EL_r over a polynomial ring; this asks that one specific family of asymptotic representations of E_20 of a free path algebra be roundable.
  leavitt-st20-is-a-quotient-of-its-kazhdan-cone-half: that is the established reduction; this is its single open prerequisite.
---

**OPEN.** Notation of `leavitt-st20-is-a-quotient-of-its-kazhdan-cone-half`: `R = L_(F_2)(1,2)`,
`Delta = St_20(R)`, `Delta_+ = E_20(R_+)` with `R_+ ≅ F_2 Q`, and `φ_* : Delta_+ ->> Delta`.

```text
(PR)   For every asymptotic representation σ_n : Delta -> U(d_n) (normalized HS), there are genuine
       λ_n : Delta_+ -> U(D_n) with D_n >= d_n, D_n/d_n -> 1 and
       ||σ_n(φ_* g) - P_n λ_n(g) P_n*||_2 -> 0 for every g in Delta_+.
```

**Status of the equivalence.** `(PR)` holds iff `Delta` is not hyperlinear (item 5 of the reduction).
So `(PR)` is flagship-level for this one group. It is the only open input on this route.

**Sufficient condition.** `Delta_+` is flexibly HS-stable. `Delta_+` is residually finite, Kazhdan
and perfect. Strict HS-stability is excluded by `infinite-hyperlinear-kazhdan-group-is-not-hs-stable`.

**What a proof of (PR) may not use.**
- The finite-dimensional head bound is already a theorem: `(QN)`, item 4 of the reduction. Any
  genuine rounding `λ_n` is automatically near trivial.
- So a proof of `(PR)` for a hyperlinear approximation `σ_n` is impossible, since hyperlinear
  approximations have non-roundable pullbacks.
- A proof must therefore show that every asymptotic representation of `Delta` is asymptotically
  trivial, or prove stability of `Delta_+` for all asymptotic representations.

**What a refutation needs.** A hyperlinear approximation `σ_n` of `Delta`. Its pullback is then an
explicit non-roundable asymptotic representation of `Delta_+`.
