---
rg: 2
id: threshold-free-reverse-kleene-higman-diagonal
kind: claim
title: Reverse Kleene needs only qualitative hyperlinear-radical collapse and a recursively enumerable presentation
distinct_from:
  kleene-halting-mark-collapse-diagonal: that asks the compiler to output computable defect and marked-distance thresholds for a finite presentation; this needs no numerical modulus and allows a uniformly recursively enumerable relator stream before the fixed point.
  group-algebra-mark-reverse-kleene-collapse: that proves the threshold-free argument for a finite presentation and a rational group-algebra mark; this extends the word-mark form to uniformly recursively presented groups and then applies effective Higman embedding.
  dimension-kleene-threshold-needs-amplification-envelope: that is a no-go for the opposite matrix-search orientation, whose program must enter a dimension-dependent threshold; this proof-enumeration orientation never reads a matrix dimension or a soundness threshold.
---

Suppose a total computable compiler sends every Turing-machine index `e` to:

- a finite generating alphabet `S_e`;
- a uniformly recursively enumerable relator stream `R_e`; and
- a marked word `w_e`.

Put `Gamma_e=<S_e|R_e>`.  Assume

```text
machine e halts     => w_e != 1 in Gamma_e,             (TFK1)
machine e does not halt
                    => w_e lies in Rad_hyp(Gamma_e).    (TFK2)
```

Then one can effectively construct a finitely presented non-hyperlinear
group.  The fixed-point program needs no defect threshold, marked cutoff,
decoder modulus, matrix dimension, convergence rate, or runtime bound.
