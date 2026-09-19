---
rg: 2
id: ideal-central-components-retain-an-amenable-nonqd-witness-proof
kind: route
title: Use the amenable face and convexity of QD matrix models
target: ideal-central-components-retain-an-amenable-nonqd-witness
requires:
  - amenable-nonqd-descends-liftable-quotients
artifacts:
  - research/artifacts/stw10-amenable-trace-frontier-2026-08-30.md
---

The normal extension `tau**` is tracial on `A**`, and `z` is central, so the
functionals in (1) are tracial states.  Moreover,

```text
tau = alpha tau_I + (1-alpha) tau_Q.                  (2)
```

Amenable traces form a face in the tracial state space (Brown, Theorem
3.1.6 and its face consequence).  Since `tau` is amenable, (2) makes both
components amenable whenever their coefficients are nonzero.

Quasidiagonal traces are convex.  Indeed, given QD matrix models for two
traces and a desired coefficient `alpha`, take block-diagonal direct sums
with multiplicities whose normalized block sizes approximate `alpha`.
Multiplicative defects are the maximum of the two block defects, while the
normalized matrix traces converge to the desired convex combination.
Therefore, if both components in (2) were QD, then `tau` would be QD.  At
least one component is consequently amenable and non-QD.  The endpoint cases
have only one nonzero summand and are immediate.

For `x in I`, `(1-z)x=0`, so `tau_Q(x)=0`.  It factors through a trace on
`A/I`.  If the quotient is locally liftable and `tau_Q` is the non-QD
component, `amenable-nonqd-descends-liftable-quotients` gives the final
assertion.

**Trust boundary.**  The bidual central-support description of ideals and
Brown's theorem that amenable traces form a face are imported.  Convexity of
QD traces and the component/quotient calculations are proved directly.  The
claim does not assert the open stronger statement that QD traces form a face.
