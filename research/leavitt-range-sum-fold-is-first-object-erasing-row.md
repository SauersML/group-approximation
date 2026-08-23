---
rg: 2
id: leavitt-range-sum-fold-is-first-object-erasing-row
kind: claim
title: The relative Leavitt range-sum fold is the first object-erasing Steinberg row
distinct_from:
  outer-root-leavitt-table: that realizes the two diagonal and two crossed-zero coefficient products through commuting outer roots; this adds the two range products and compares their sum with one diagonal return in the identical long root.
  mixed-steinberg-loops-admit-morita-rectangular-model: that proves every well-typed triangle pasting survives in the two-object Morita model; this identifies the smallest native word which is not a well-typed pasting because it folds the source and target object units together.
  affine-leavitt-source-saturated-reynolds-checksum: that asks for a finite-matrix adjoint Gram estimate; this identifies the fixed group word whose same-output-root decoding would have to supply that estimate.
  leavitt-range-sum-fold-does-not-pay-reynolds: that tensors independent central-character UT4 path packets with the rectangular Weyl cell and proves the fold word itself is still insufficient; this identifies the fold as the first necessary row, not as a standalone decoder.
---

**ESTABLISHED ALGEBRAIC REDUCTION.**  Work in the relative Leavitt ring with
active idempotent `A` and

```text
t_i s_j=delta_(ij)A,          s_0t_0+s_1t_1=A.          (LRF1)
```

Use four Steinberg indices and define the three commuting-outer-root path
words

```text
D   =[x_12(A t_0),[x_23(1),x_34(s_0 A)]],
C_i =[x_12(A s_i),[x_23(1),x_34(t_i A)]]   (i=0,1).    (LRF2)
```

The Steinberg commutator formula and `(LRF1)` give

```text
D=x_14(A t_0s_0 A)=x_14(A),
C_i=x_14(A s_it_i A),
C_0C_1=x_14(A(s_0t_0+s_1t_1)A)=x_14(A).                (LRF3)
```

Consequently the single fixed word

```text
r_fold=C_0C_1D^(-1)                                    (LRF4)
```

is trivial in the full affine-Leavitt Steinberg group.  For any fixed finite
presentation its evaluated normalized-HS defect is bounded by a fixed
multiple of the presentation defect, because `(LRF3)` has a fixed Steinberg
derivation.

This row is categorically different from every presently audited mixed
triangle.  In the Morita rectangular model, `D` is the source-object identity
`1_E`, while `C_0+C_1` is the target-object identity `1_F`, with
`F=E direct_sum E`.  Each equality in `(LRF3)` before the final comparison is
well typed and exact, but `(LRF4)` erases the object type and asks the two
outputs to be the **same** `X_14(A)` root coordinate.  It therefore does not
belong to the triangle/associativity language covered by
`mixed-steinberg-loops-admit-morita-rectangular-model`.

It is minimal in the native coefficient-path language.  One diagonal return
is needed to name `1_E`.  Neither target branch alone names `1_F`; both range
terms are needed because only `s_0t_0+s_1t_1=A`.  Thus an object-erasing
comparison needs at least the three products appearing in `(LRF4)`.

This does **not** prove a normalized-HS payment.  A group microstate controls
the one output word `(LRF4)`, but the desired Reynolds leakage lives on the
whole multiplicity commutant of the source packet.  The remaining assertion
is a same-output-root decoder: on the prescribed marked carrier, decoding
the three occurrences in `(LRF2)` must make the fold defect charge

```text
||(I-R_1) Ad(U_0) R_s||_(HS,ad)^2.                      (LRF5)
```

By `leavitt-branch-reynolds-return-has-rectangular-gap`, `(LRF5)` is
equivalently a lower bound on one explicit finite average of squared traces
of the cross words `Y_hU_0S_gU_0^*`.  Thus the unresolved decoder has a
finite scalar output; it need not reconstruct a basis of the growing
multiplicity commutant.

The output equality alone cannot provide that lower bound.
`leavitt-range-sum-fold-does-not-pay-reynolds` constructs an exact
packet-plus-fold model retaining the positive leakage `(LRF5)`.  Thus the
missing decoder must also identify the fold's coefficient **occurrences**
with the branch packet maps; it cannot treat the three long-root outputs as
independent central-character gadgets.

Without that matrix-coordinate decoding, `(LRF4)` is only equality of one
long-root observable and does not identify its multiplicity reservoir.
Accordingly the smallest native word has now been found; the unresolved
mathematics is promotion of its scalar/root equality to the adjoint
same-reservoir estimate `(LRF5)`.
