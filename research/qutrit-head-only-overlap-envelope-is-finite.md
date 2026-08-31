---
rg: 2
id: qutrit-head-only-overlap-envelope-is-finite
kind: claim
title: A qutrit phase marginal coupled only to the Jacobson head still has a finite envelope
artifacts:
  - research/qutrit-head-only-finite-envelope-proof.md
distinct_from:
  binary-jacobson-constant-q-root-envelope-is-finite: that treats the native two-qubit head packet and constant Weyl transports in rank five; this treats the 27-leaf qutrit phase packet and computes its maximal scalar-plus-head envelope in rank 28.
  four-root-qutrit-bridge-is-jacobson-core: that adjoins raw S and T roots and reaches the full Jacobson elementary group; this omits those raw occurrences and proves the remaining head-only package is finite.
  thompson-27-cylinder-qutrit-cell-is-fd-invisible: that constructs the proper three-phase marginal inside the finite packet and embeds it in minimally almost periodic hosts; this shows why attaching only a head root does not make that marginal load-bearing.
---

In the outer 27-leaf chart, put

```text
Q=1-s_0t_0=s_1t_1,        A_Q=F_2[Q].
```

Let `F` be the transitive qutrit packet and, for `n>=2), define

```text
H_Q=<D_n(F),e_12(s_0),e_21(t_0),e_12(s_0Q)> <= EL_n(R).
                                                               (QHF1)
```

Then

```text
H_Q isomorphic to EL_28(A_Q)
    isomorphic to GL_28(F_2) x GL_28(F_2).                (QHF2)
```

In particular `H_Q` is finite.  The conclusion is unchanged if finitely
many further roots with coefficients in `A_Q` are added.

The proper qutrit marginal with coefficientwise three-phase cancellation
lies in `C[F]<=C[H_Q]`, and the head root `x_ij(Q)` lies in
`H_Q`.  Nevertheless the left regular representation of the finite group
`H_Q` retains both with every algebraic overlap relation exact.  Hence no
finite additive atlas supported only by the qutrit packet, scalar chart, and
head-labelled roots can prove nonhyperlinearity.

For `n>=5`, adjoining the corresponding standard Steinberg root lifts to
the lifted packet gives a central-by-finite, amenable, hyperlinear group.
Thus the first eligible qutrit/head overlap must visibly consume at least one
raw `S`- or `T`-bearing occurrence in the same coefficient incidence;
the idempotent head `Q` by itself is another finite envelope.
