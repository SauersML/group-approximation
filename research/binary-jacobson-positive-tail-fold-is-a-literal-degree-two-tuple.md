---
rg: 2
id: binary-jacobson-positive-tail-fold-is-a-literal-degree-two-tuple
kind: claim
title: The positive-tail Jacobson fold is a literal compressed degree-two root tuple on the raw range
artifacts:
  - research/binary-jacobson-positive-tail-literalization-proof.md
distinct_from:
  binary-jacobson-tail-phase-cannot-correct-closing-fold: that computes the PI degree and the failure of spectral phase corrections abstractly from branch parity; this identifies every surviving folded row as the compression of a named Jacobson root.
  binary-jacobson-head-sector-has-native-two-qubit-packet: that gives the literal degree-four target tuple on the head cut; this puts the literal degree-two source and that target on the same raw range projection.
  binary-jacobson-first-alternating-ts-closure-relation: that identifies the first relation coupling the raw coefficients to the remaining opposite root; this supplies the exact source coefficients on which that relation must act.
---

**ESTABLISHED.**  Take the unphased closing fold `T=2^(-1/2)R(1+b)` and
the positive tail range `F_+` from
`binary-jacobson-tail-phase-cannot-correct-closing-fold`.  On `F_+`, the
folded native tuple is exactly

```text
T(X_0,Z_0,X_1,Z_1)T^*
 =F_+ (x_12(S^2), 0, x_14(SQ), x_43(1)) F_+.            (JLT1)
```

All three nonzero root words reduce `F_+`.  The last two form a Pauli pair
with center `x_13(SQ)=-1` on this raw range, while `x_12(S^2)` commutes with
them.  Therefore `(JLT1)` is a completely occurrence-typed tuple in a
quotient of `M_2 directSum M_2` and satisfies `s_4=0`.

At the same time the original native tuple

```text
D=(x_12(Q),x_23(1),x_14(Q),x_43(1))|_(F_+)             (JLT2)
```

still generates `M_4 tensor I`, because `F_+` is a nonzero reducing
subprojection of the negative head cut.  Thus the source and target PI
degrees now live on the **same literal projection**, and every nonzero source
entry is a named group-word compression.  No abstract packet isomorphism or
untyped Schur gauge remains.

The missing assertion is only a common square return in the `F_+` corner.
The first alternating relation of
`binary-jacobson-first-alternating-ts-closure-relation` is eligible because
its root `x_21(T)` detects `x_14(SQ)` while commuting with `x_14(Q)`; whether
the polar of `F_+x_21(T)F_+` has full support and authenticates all four
rows remains open.

DERIVATION
binary-jacobson-positive-tail-literalization-proof
