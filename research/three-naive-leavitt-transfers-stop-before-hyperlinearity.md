---
rg: 2
id: three-naive-leavitt-transfers-stop-before-hyperlinearity
kind: claim
title: Three naive Leavitt transfers stop before hyperlinearity
distinct_from:
  direct-finiteness-not-inherited-by-quotients: that isolates the quotient-permanence failure; this combines it with the scalar-characteristic and normalized-HS failures and locates the surviving direct Leavitt gate.
  complex-hyperlinear-leavitt-idempotent-mismatch: that treats the explicit order-three corner; this audits all three transfer families.
  hs-full-rank-scalar-defect-blocks-naive-rank-decoding: that blocks unstructured HS-to-rank conversion; this also records the quotient and characteristic failures and the remaining same-coordinate decoder.
  atlas-hard-packet-s3-channel-decoder: that is the open positive decoder claim; this is the no-go audit explaining why the three shortcuts do not supply it.
artifacts:
  - research/artifacts/kaplansky-direct-finiteness-audit-2026-08-17.md
  - research/artifacts/hs-to-rank-naive-decoder-no-go-2026-08-21.md
  - notes/FALSE_DETERMINANT_INDEX_TO_PHASE_HS_EXTENSION.md
---

Let `R=L_(F_2)(1,2)` and `G=R^x`. Three tempting transfers from the
non-directly-finite Leavitt algebra to complex unitary microstates fail for
independent, exact reasons.

1. **Quotient transfer fails.** Evaluation gives a surjection
   `F_2[G] ->> R`, but direct finiteness does not pass backwards from a
   quotient. A directly finite domain can have a non-directly-finite
   quotient, so the Leavitt image does not prove that `F_2[G]` is not directly
   finite.
2. **Scalar transfer fails.** For the explicit order-three unit `g`, the
   characteristic-two element `[g]+[g^2]` is an idempotent evaluating to
   `1_R`. In every complex representation the formally identical element
   `a=u_g+u_(g^2)` instead satisfies `a^2-a=2I`. The genuine complex spectral
   projection `(2-u_g-u_(g^2))/3` has no evaluation into `R` and carries no
   binary Leavitt relation.
3. **Metric transfer fails.** Normalized-HS-small defects need not have
   small normalized rank: `(exp(i epsilon)-1)I_d` has full rank for every
   nonzero `epsilon` while its normalized HS norm can tend to zero. Nor does
   determinant phase repair this loss: rank-one determinant flips and
   winding-one loops are uniformly normalized-HS null. Thus neither a naive
   rank decoder nor a determinant central cover descends from the tracial
   metric alone.

These are no-go statements about proof mechanisms, not a decision on whether
`G` is hyperlinear. In particular they do not rule out a presentation-level
spectral gap, a Kervaire--Laudenbach obstruction, or another invariant using
more of the group relations.

For the current direct binary-Leavitt atlas lane, the narrowest surviving gate
is `atlas-hard-packet-s3-channel-decoder`. After the established finite `S_3`
coefficient transforms, the literal full hard/interior/comb packet must
satisfy

```text
rank [C D] = rank D + 3,
```

where `C` consists of the three desired common-coordinate path products and
`D` consists of every nuisance multiplicity monomial in the selected rows.
Equivalently, the packet must provide a dimension-free nuisance-annihilating
left inverse yielding

```text
||R0^* W L0-W||_2 -> 0,
||R1^* W L1-W||_2 -> 0,
||R0^* W L1||_2   -> 0.
```

That output feeds `finite-window-decoder` on its fixed trace-`1/8` corner and
then `leavitt-multiplicative-trace-floor`. A minor before quotienting by `D`,
a carrier-only identity, or any one of the three transfers above is not this
gate.
