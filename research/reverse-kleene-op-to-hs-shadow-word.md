---
rg: 2
id: reverse-kleene-op-to-hs-shadow-word
kind: claim
title: Compile NONHALT into one operator-to-HS shadow-erased word
root: true
distinct_from:
  threshold-free-reverse-kleene-mf-higman: that asks NONHALT to kill the word in every norm corona; this target asks only for normalized-HS erasure of operator-norm microstates.
  threshold-free-reverse-kleene-higman-diagonal: that asks for erasure across all HS microstates; this target restricts to the narrower class arising as shadows of operator-norm almost representations.
  reverse-kleene-operator-norm-collapse-gives-non-mf: that asks for a dimension-independent operator-norm collapse threshold; this target is qualitative and threshold-free.
artifacts:
  - research/artifacts/shadow-kleene-saturation-compiler-2026-08-22.md
---

Construct a total computable compiler sending each Turing-machine index `e`
to a finite alphabet, a uniformly recursively enumerable relator stream
presenting `Gamma_e`, and a word `w_e`, with

```text
HALT(e)    => w_e != 1 in Gamma_e,
NONHALT(e) => w_e in R_{infinity->2}(Gamma_e).
```

The NONHALT clause quantifies only over normalized-HS shadows of
operator-norm almost representations.  No positive-density carrier,
dimension report, numerical threshold, convergence modulus, or direct
operator-norm collapse is required.  By
`shadow-kleene-saturation-metatheorem`, completing this target yields a
2-generated finitely presented AH Kazhdan group with full MF radical.

## Attempts

1. **One-sided Kazhdan compression:** successful as an unconditional fixed
   shadow bug (`fournier-facio-hnn-single-shadow-bug`), but it does not yet
   encode machine-dependent HALT/NONHALT semantics.
2. **Fanizza/central-word BCS compiler:** the previous all-HS target stops at
   a forbidden-sector or multiplicity extraction gate.  Re-audit it against
   the narrower operator-to-HS model class; positive-density survival is no
   longer part of the specification.
3. **Atlas/arithmetic/projective compilers:** existing routes still seek
   multiplicity-independent nonlinear-to-linear HS estimates.  Test whether
   operator-norm hypotheses exactify the relevant finite relations before
   averaging, which would suffice for shadow erasure.
4. **Dimension-report self-search:** rejected.  A post-hoc threshold
   `delta(d)` need never be crossed by an unknown defect profile.  The target
   is deliberately qualitative so the fixed-point stage can search proofs
   rather than matrices.
