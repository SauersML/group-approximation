---
rg: 2
id: ideal-central-components-retain-an-amenable-nonqd-witness
kind: claim
title: Every ideal splits an amenable non-QD trace with a non-QD central component
distinct_from:
  amenable-nonqd-descends-liftable-quotients: that treats a trace which already vanishes on the ideal and uses local liftability to descend it; this first decomposes an arbitrary counterexample trace by the ideal support inside the bidual.
  stw99-problem-x1-amenable-traces-quasidiagonal: this localizes a hypothetical counterexample but does not produce one or prove that QD traces form a face.
artifacts:
  - research/artifacts/stw10-amenable-trace-frontier-2026-08-30.md
---

Let `tau` be an amenable non-quasidiagonal tracial state on a unital
C*-algebra `A`, let `I` be an ideal, and let `z in Z(A**)` be the central
support projection with `I**=A**z`.  Put `alpha=tau**(z)`.

If `0<alpha<1`, define tracial states on `A` by

```text
tau_I(a)=tau**(az)/alpha,
tau_Q(a)=tau**(a(1-z))/(1-alpha).                      (1)
```

Then both `tau_I` and `tau_Q` are amenable, and at least one of them is not
quasidiagonal.  The same conclusion, with the sole nonzero component, holds
when `alpha` is `0` or `1`.

The quotient component `tau_Q` vanishes on `I`.  If it is the non-QD
component and `A -> A/I` is locally liftable, it induces an amenable non-QD
trace on `A/I`.
