---
rg: 2
id: packet-central-active-complement-reduces-shared-words
kind: claim
title: A packet-central analytic exit complement approximately reduces every shared word
distinct_from:
  mixed-cnot-allowed-active-return: that must place the reducing complement in the next recurrent carrier; this proves only the local reducing-corner estimate and does not name the complement by a scalar group word.
  projected-hard-sign-bridge-selects-joint-exit: that transports the nonlinear exit after right compression; this controls the complementary projection against the current shared algebra.
---

Let `J,K,b` be commuting self-adjoint involutions and put

```text
Q=(I-J)/2,       F=(I-K)/2,       B=(I-b)/2,
X=QFB,           A=Q-X.                                  (PAC1)
```

Then `X<=Q` and `A` are projections.  For every unitary `Y`,

```text
||[Y,A]||_2
 <= ||[Y,J]||_2
    +(1/2)||[Y,K]||_2+(1/2)||[Y,b]||_2.                 (PAC2)
```

Consequently

```text
||(I-A)YA||_2 <= ||[Y,A]||_2.                           (PAC3)
```

If the three packet endpoint involutions commute exactly with the current
shared BCS generators, `A` reduces the entire shared BCS algebra exactly.
If their commutator relators have total squared normalized-HS energy `E`,
every fixed shared word `W` of length `L` has leakage at most

```text
||(I-A)W A||_2 <= C L sqrt(E),                          (PAC4)
```

for an absolute choice of `C`.  The estimate is dimension-independent and
does not require `A`, `X`, or their reflections to be group words.

This closes the reducing-corner clause of the allowed-active-return problem.
It does not identify `A` with a next-level carrier.  That remaining placement
must be one-sided or properly infinite on the completeness representation;
an ordinary scalar word cannot recognize the three-atom complement in
`(PAC1)`.
