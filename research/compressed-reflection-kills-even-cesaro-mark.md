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

This theorem does **not** apply directly to the native Fanizza uniform-clock
carrier. As corrected in `uniform-clock-corner-is-not-a-reflection`, the
full controlled operator `C` satisfies `C^2=1`, but

```text
Q C Q=(1-H_m) tensor Q
```

is not a unitary in the `Q` corner unless `H_m=0`. Its complementary
leakage is exactly `H_m(2-H_m)`. Thus the Fanizza application still needs
a genuinely reducing returned carrier, or an independent weighted-state
argument controlling the excursions of powers of the prospective word.
The abstract estimate `(CRK2)` remains valid under its displayed hypotheses.
