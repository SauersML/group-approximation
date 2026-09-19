---
rg: 2
id: kt-shulman-profinite-vertex-model-is-nontempered
kind: claim
title: The profinite Shulman model fails the reduced gate already on one Kun--Thom vertex
distinct_from:
  weak-mf-embedding-not-reusable: that gives a universal padding and metric-change firewall for an arbitrary fixed weak-MF embedding; this exhibits a fixed group-ring Markov element with a strict norm gap in the actual profinite regular vertex model.
  shulman-symmetric-double-has-no-stable-trace-upgrade: that audits the scope of Shulman's theorem and says it selects no prescribed trace; this proves the stronger candidate-specific fact that the input representation is not reduced-norm continuous even before amalgamation.
  kt-double-reduced-cstar-is-mf: that is the positive reduced-algebra certificate; this rules out only its direct derivation from the existing profinite regular model and does not refute the certificate.
artifacts:
  - notes/WEAK_MF_NONSOFIC_DOUBLE.md
---

**ESTABLISHED.**  Let `G` be the nonamenable residually finite vertex group
in the `q=2` Kun--Thom pair.  Fix a finite symmetric generating set `S` and
put

```text
m=|S|^(-1) sum_(s in S) s in C[G].                       (KPV1)
```

For every finite quotient `q:G->Q`, the finite-quotient regular
representation has

```text
||lambda_Q(q(m))||=1,                                    (KPV2)
```

because the constant vector is fixed.  On the other hand Kesten's criterion
gives

```text
||lambda_G(m)||<1.                                       (KPV3)
```

Consequently the residual finite-quotient regular representation used to
build the MF vertex algebra in `symmetric-double-weak-mf-proof` is not
continuous for the reduced norm.  Its norm-corona map cannot factor through
`C*_r(G)`, and therefore the associated application of Shulman's symmetric
amalgam theorem cannot descend directly to `C*_r(G *_Gamma G)`.

This obstruction is upstream of mixed-word trace selection: it occurs on a
single vertex.  It also explains why an abstract regular trace on the MF
completion is insufficient.  That trace has the correct values on group
elements, while the completion still assigns norm `1` to `(KPV1)` instead of
the strictly smaller reduced norm.

The result does not say that `C*_r(G)` or the reduced double is non-MF.  A
positive construction may use entirely different matrix models (for
example, deleting the constant summand removes this particular witness but
does not prove convergence of all reduced norms).

DERIVATION
kt-shulman-profinite-vertex-nontempered-proof

