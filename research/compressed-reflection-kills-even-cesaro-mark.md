---
rg: 2
id: compressed-reflection-kills-even-cesaro-mark
kind: claim
title: An approximately compressed reflection kills every fixed even Cesaro marked sum
distinct_from:
  wandering-mark-cesaro-amplifier: that converts a finite-matrix Cesaro ceiling and regular wandering into nonhyperlinearity; this derives the finite-matrix ceiling directly from one compressed-reflection estimate.
  uniform-clock-reflection-block-encodes-game-hamiltonian: that constructs the verifier reflection and its marked Dirichlet inequality; this controls powers of an ordinary unitary whose selected compression approximates that reflection.
---

Let `(M_d(C),tau_d)` carry a projection `Q`, a self-adjoint partial unitary
`V=QVQ` with `V^2=Q`, a unitary `W`, and a positive contraction `D` such
that

```text
D=QDQ,              D <= C(Q-V).                       (CRK1)
```

Put

```text
epsilon=||QWQ-V||_2,
Sigma_t(W)=1+W+...+W^(t-1).
```

For every even `t`,

```text
||D^(1/2) Sigma_t(W)||_2^2
 <= (t(t-1)/2)^2 (epsilon^2+2epsilon).                 (CRK2)
```

In particular, for each fixed even `t`, an `o(1)` compressed-reflection
error gives an `o(1)` marked Cesaro norm.  No weighted-state Dirichlet
comparison is additionally required.

Applied to the Fanizza clock reflection, take `D` to be the clock-amplified
native losing projection.  The established inequality

```text
D <= C_m Q(1-V_m)Q
```

is `(CRK1)`.  Therefore clauses 1--2 of
`fanizza-coherent-verifier-wandering-promotion`, together with its normal
form clause, already feed `wandering-mark-cesaro-amplifier`: choose one fixed
even `t`, absorb the right side of `(CRK2)` into the microstate modulus, and
use pairwise distinctness of `w^k` and `X_D^R w^k` for canonical norm
`t/2`.

The estimate also sharpens the remaining construction problem.  It is enough
to produce the single corner approximation `QWQ approximately V_m`; one
does not have to compare the Fanizza Hamiltonian with the Dirichlet form of
`W` on the non-invariant Cesaro-weighted state.
