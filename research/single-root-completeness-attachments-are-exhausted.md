---
rg: 2
id: single-root-completeness-attachments-are-exhausted
kind: claim
title: One extra root has no completeness attachment beyond the existing fold fences
artifacts:
  - experiments/single_fold_root_incidence_audit.py
distinct_from:
  leavitt-range-sum-fold-is-first-object-erasing-row: that identifies the first same-output-root additive word; this classifies every possible position of one further root attached to that word.
  intermediate-fold-arm-has-finite-s6-model: that gives a finite model after one composable root creates a named intermediate arm; this proves that composable case and the opposite case exhaust all noncommuting one-root geometries.
  native-opposite-arm-return-has-finite-s6-model: that authenticates the literal s_0 and t_0 occurrences and an opposite partial Whitehead in one selected branch; this shows there is no different one-branch native specialization hidden inside the composable case.
  reverse-product-whitehead-fold-has-finite-fusion: that treats separate opposite-root copies of the two child coefficients and the parent; this identifies it as the strongest coefficient-sensitive specialization of the unique opposite-root case.
---

**ESTABLISHED SHORTEST-WORD FENCE.**  Put

```text
C_0=x_ab(p),          C_1=x_ab(q),          J=x_ab(1),
p=s_0t_0,             q=s_1t_1,             C_0C_1=J. (SRA1)
```

Fix one further root position `beta=(c,d)`.  Up to reversing the displayed
commutator and permuting spare indices, exactly one of the following occurs.

1. `beta=(b,k)` or `(k,a)` is composable with `(a,b)`.  The only new
   ordinary Steinberg row is respectively

   ```text
   [C_i,x_bk(r)]=x_ak(q_i r),
   [x_ka(r),C_i]=x_kb(r q_i).                          (SRA2)
   ```

   Multiplying the two child outputs gives the parent output.  This is
   exactly the propagated intermediate-fold cell, on the right or on the
   left.
2. `beta=(b,a)` is opposite.  The new bounded words are rank-one alternating
   words.  When the coefficient is tied to `p`, `q`, and `1`, their shortest
   coefficient-sensitive closure is the child/parent partial-Whitehead
   table of `reverse-product-whitehead-fold-has-finite-fusion`.
3. `beta` has the same source, the same target, or is distant from `(a,b)`.
   The ordinary root occurrences commute.  They add no coefficient reader.

There is no fourth incidence type.  The `A_4` enumeration in
`experiments/single_fold_root_incidence_audit.py` checks all `19` root
positions distinct from `(a,b)`: one opposite, six composable, six sharing
only source or target, and six distant.

The two noncommuting cases already have exact marked finite fences.  The
composable case remains finite even after naming and transporting its
intermediate arm (`intermediate-fold-arm-has-finite-s6-model`), and even
after specializing the coefficient to the literal `s_0,t_0` Morita arms and
placing the intermediate arm in its opposite partial Whitehead
(`native-opposite-arm-return-has-finite-s6-model`).  The opposite case
remains finite after both child reverse products and their parent are used
essentially in the nonlinear completeness word
(`reverse-product-whitehead-fold-has-finite-fusion`).

Therefore no new shortest completeness-to-mark word can be obtained by
attaching only one new root position to `(SRA1)`, nor by giving its one
composable intermediate arm the already-audited native return.  A live word
must use at least two additional root positions and a relation between those
new occurrences which is not a pasting of branchwise returns.  In the
current compiler this is precisely the relative-reservoir lock left after
the mixed cross-zero and returned-source fences.

This classification concerns the one-root ordinary commutator/partial-
Whitehead closure.  It does not claim that every finite subsystem of the
full Leavitt Steinberg presentation has a marked model.

DERIVATION
single-root-completeness-attachment-classification
