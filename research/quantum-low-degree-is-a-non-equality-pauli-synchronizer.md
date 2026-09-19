---
rg: 2
id: quantum-low-degree-is-a-non-equality-pauli-synchronizer
kind: claim
title: The quantum low-degree test synchronizes a growing Pauli family without equality clouds
distinct_from:
  pauli-braiding-test-constant-robustness: that uses the long-question linearity test; this records the point-plane algebraic synchronizer and the exact parameters relevant to occurrence groupification.
  expander-cloud-reduction-preserves-pauli-dimension-gap: that synchronizes duplicated occurrences by equality expanders; this decoder uses one global low-degree measurement and introduces no sheet factor.
---

ESTABLISHED.  Established by Natarajan--Vidick, *Low-degree testing for quantum states,
and a quantum entangled games PCP for QMA*, arXiv:1801.03821, Theorem 3.2.
For integers `h,m` with `h^m>=n`, total degree `d=hm`, and a prime power
`q=p^t` admitting a self-dual basis over `F_p`, their two-prover quantum
low-degree test has:

1. perfect completeness;
2. robustness

```text
delta = poly(poly(p) poly(epsilon) + poly(d/q));                (QLD1)
```

3. a soundness isometry extracting `n` qudits of local dimension `q` and
   the associated generalized Pauli measurements.

Consequently a strategy within a sufficiently small constant of one, with
`d/q` below a sufficiently small constant, has original local dimension at
least

```text
q^n.                                                            (QLD2)
```

The dimension conclusion is on the original strategy: a local isometry
extracting `n` EPR qudits cannot increase Schmidt rank.  It therefore has no
covering-sheet or Naimark-dilation loss.

The mechanism is a genuine non-equality synchronizer.  In each of the X and
Z bases the questions are points and affine two-planes in `F_q^m`.  A plane
answer is a polynomial restriction and a point answer is one evaluation.
Entangled low-degree soundness recovers one global polynomial measurement,
then the commutation/Magic-Square component couples the recovered X and Z
families.  No connected graph of pairwise equality copies is used in that
recovery.

This proves that the analytic object sought after
`equality-synchronized-lifts-create-two-pair-contours` exists in a
higher-arity form.  It does **not** yet give a finite-template group
compiler: the field/answer packet and the raw incidence degrees grow, as
recorded in `quantum-low-degree-is-not-a-direct-finite-template-compiler`.
