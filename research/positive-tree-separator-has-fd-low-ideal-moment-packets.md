---
rg: 2
id: positive-tree-separator-has-fd-low-ideal-moment-packets
kind: claim
title: A positive tree separator has finite-dimensional packets retaining its gap with arbitrarily small prescribed ideal moments
distinct_from:
  tree-face-separator-signedness-is-removable-modulo-the-unit: that produces a positive Choi state on a matrix amplification of the quotient; this pulls it back to the RFD relator algebra and approximates the same state by finite-dimensional vector packets while preserving both the tree value and finitely many ideal moments.
  km-triangle-relative-gap-failure-has-fd-full-support-witnesses: that produces full-ideal-support packets with low relator energy independently of a quotient separator; this correlates low prescribed ideal moments with the positive tree-defect value forced by a separator, but does not force full ideal support.
  finite-relator-reservoir-repairs-every-fd-packet: that asks for operator-level Choi feasibility for every packet using one reservoir; this gives one vector-state packet for each finite reservoir and tolerance and therefore does not decide uniform repair.
---

**ESTABLISHED (correlated finite-dimensional approximation).**  Use the
Kac--Moody triangle notation

```text
A=C^*(G_0),       q:A->>Q=C^*(Lambda),       I=ker q.       (PTF1)
```

Assume a quotient separator with gap `delta` exists.  By
`tree-face-separator-signedness-is-removable-modulo-the-unit`, for one tree
face `H` there are a finite Choi algebra

```text
D_Q=direct_sum_r M_(n_r)(Q),
```

a state `omega` on `D_Q`, and a self-adjoint Choi defect `X in D_Q` such that

```text
omega(X)>=c_H delta>0.                                    (PTF2)
```

Put `D_A=direct_sum_r M_(n_r)(A)` and let `q_D:D_A->>D_Q` be the amplified
quotient.  For every self-adjoint lift `X_tilde` of `X`, every finite set

```text
Y subset ker q_D=direct_sum_r M_(n_r)(I),
```

and every `epsilon>0`, there are a finite-dimensional representation
`Pi:D_A->M_N` and a unit vector `xi` such that

```text
<Pi(X_tilde)xi,xi> >= c_H delta-epsilon,                   (PTF3)
sum_(y in Y)||Pi(y)xi||^2 < epsilon.                       (PTF4)
```

Every finite-dimensional representation of `D_A` is assembled from
amplifications of finite-dimensional representations of `A`.  Thus
`(PTF3)--(PTF4)` are literal finite-dimensional representation packets of
the virtually free group `G_0`.  Taking `Y` to contain a basis of any fixed
matrix-amplified relator reservoir makes all its prescribed vector moments
arbitrarily small while the same packet retains a fixed positive fraction of
the tree-separator gap.

**Sharp scope.**  This is stronger than the uncorrelated low-spectrum packets:
tree defect and ideal smallness occur in the same vector state.  It still
does not close the finite-reservoir problem for three independent reasons.

1. `(PTF4)` is vector-state `L^2` control, not operator-norm smallness and not
   vanishing on the whole finite-dimensional packet.
2. The packet may contain a quotient/trivial summand.  The tree defect
   `id-M_(P_13)` need not vanish under the augmentation character, so deleting
   that summand can destroy `(PTF3)`.
3. The uniform repair problem asks that one affine ideal reservoir meet the
   relative-unital Choi cone for **every** packet.  Producing one low-moment
   vector packet for each reservoir gives neither feasibility nor
   infeasibility of that operator-level intersection.

Proof: `pull-back-the-positive-choi-state-and-use-rfd-state-density`.

DERIVATION
pull-back-the-positive-choi-state-and-use-rfd-state-density
