---
rg: 2
id: jacobson-coherent-group-is-an-ascending-corner-extension
kind: claim
title: The faithful coherent group is the ascending HNN extension of the rank-three Jacobson group by its corner embedding
distinct_from:
  jacobson-coherent-quotient-is-faithful-and-has-mf-dichotomy: that authenticates the bilateral group and its MF alternatives; this identifies its unilateral base, endomorphism, and faithful ascending normal form.
  binary-jacobson-active-cycle-generates-rank-three: that generates the rank-three base from a balanced shift and constants; this identifies the entire coherent group after adjoining the bilateral stable letter.
artifacts:
  - research/artifacts/jacobson-coherent-group-is-an-ascending-corner-extension-2026-09-08.md
---

With `J=F_2<S,T | TS=1>` and `Q=1-ST`, the faithful coherent group is

```text
Gamma_triangle ~= < M,t | t A t^(-1)=phi(A), A in M >,
M=EL_3(J),             phi(A)=Q I_3+S A T.
```

The endomorphism is proper and injective. The same nonidentity head is
`w=x_13(Q)`. Every word has a form `t^(-a) A t^b`, whose bilateral
action proves faithfulness. The height kernel is the increasing union
`union_(j>=0) t^(-j) M t^j`.

Inside the bilateral group, `M` consists exactly of operators fixing
the negative coordinate subspace pointwise **and** preserving its
nonnegative complement. The second condition cannot be omitted.

This is an algebraic identification. It does not reconstruct the ring
coefficients inside arbitrary complex matrix representations or prove
the positive operator-norm gap.

DERIVATION
jacobson-unilateral-root-extraction-and-hnn-normal-form-proof
