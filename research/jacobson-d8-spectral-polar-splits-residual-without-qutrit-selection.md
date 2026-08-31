---
rg: 2
id: jacobson-d8-spectral-polar-splits-residual-without-qutrit-selection
kind: claim
title: The separate Jacobson T-root and opposite root give two exact residual isometries but no qutrit selector
artifacts:
  - research/jacobson-d8-spectral-polar-proof.md
distinct_from:
  jacobson-residual-t-root-is-orthogonal-transport: that proves the reduced commutator has zero residual compression; this keeps the two occurrences separate and finds a full polar in each spectral branch before reduction.
  jacobson-pre-reduction-square-forces-sqrt-half-leakage: that gives an operator-norm lower bound on the off-residual leg; this computes an exact constant Gram matrix for two branchwise polar legs.
  qutrit-scalar-opposite-root-is-diagonal-or-complete: that classifies the finite scalar phase graph of the opposite root alone; this uses the mixed D8 relation and audits the raw T-root spectral ranges.
---

Put

```text
e=e_res,       t=x_23(T),       k=x_31(1),
u=[t,k]=t k t k=x_21(T).
```

The established residual identities are

```text
[t,e]=0,                  e u e=0.
```

For `eta in {+1,-1}`, define

```text
p_eta=(1+eta t)/2,        A_eta=p_eta k e.
```

Then the separate `u`- and `k`-occurrences force the exact Gram
identity

```text
A_eta^* A_eta=(1/2)e.                                  (JD81)
```

Consequently

```text
V_eta=sqrt(2) p_eta k e
```

is the polar isometry of `A_eta), with

```text
V_eta^*V_eta=e,
f_eta=V_eta V_eta^*=2p_eta k e k p_eta<=p_eta,
f_+ f_-=0.                                              (JD82)
```

Thus either raw `t`-sign branch covers the whole residual before the
commutator is reduced to `u`. This is a full-support, occurrence-typed
pre-reduction polar, not merely the lower leakage bound.

The polar has exact packet covariance whenever the packet respects the
two cuts. In particular, the alternate native two-qubit tuple

```text
D=(x_14(Q),x_43(1),x_15(Q),x_53(1))                    (JD83)
```

reduces `e`, commutes with both `t` and `u), and generates
`M_4 tensor I` on `e`. For every row `D_j`,

```text
V_eta D_j
 = (p_eta k D_j k p_eta)V_eta.                          (JD84)
```

After restricting the right-hand tuple to `f_eta`, equation `(JD84)`
is an exact typed equivalence of two degree-four packets. It therefore
does not create the desired degree-two/degree-four mismatch.

Nor does either range select a qutrit complement branch. Let
`F_q` be the order-`3^5` qutrit support group and let
`q,R,q-R in C[F_q]` be its standard projections. In the canonical
group trace,

```text
tau(f_eta)=1/32,
||f_eta q||_2^2=1/96,
||f_eta R||_2^2=1/144,
||f_eta(q-R)||_2^2=1/288.                              (JD85)
```

These are exactly the residual weights. Both orthogonal polar ranges retain
the same `2:1` split between `R` and `q-R`.

The exact two-branch polar therefore closes the support question but not the
Hall question. A decisive continuation must prove an additional covariance
which sends the two selected qutrit phases through only one complement
phase, or show that one of the two `t`-spectral ranges is deleted by a
further mixed occurrence. The D8 square itself supplies two balanced full
branches.
