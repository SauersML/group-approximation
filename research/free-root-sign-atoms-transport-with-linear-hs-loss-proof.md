---
rg: 2
id: free-root-sign-atoms-transport-with-linear-hs-loss-proof
kind: route
title: Telescope products of sign projections and sum unitary blocks
target: free-root-sign-atoms-transport-with-linear-hs-loss
requires:
  - robust-rank-one-endpoint-marginal-floor
---

Set

```text
P_i=(I+epsilon_i A_i)/2,
Q_i=(I+epsilon_i B_i)/2.                                 (SAT4)
```

Every `P_i,Q_i` is an orthogonal projection and therefore a contraction.
Unitary conjugation distributes over products.  The standard telescoping
identity gives

```text
U P U^*-Q
 =sum_i (product_(j<i) U P_j U^*)
          (U P_i U^*-Q_i)(product_(j>i) Q_j).             (SAT5)
```

Left or right multiplication by a contraction cannot increase normalized
Hilbert--Schmidt norm.  The triangle inequality and

```text
U P_i U^*-Q_i=(epsilon_i/2)(U A_i U^*-B_i)               (SAT6)
```

prove `(SAT2)`.  Tracial Cauchy--Schwarz gives
`|tau(P)-tau(Q)|<=||P-Q||_2`, proving `(SAT3)`.

For the marginal statement, let `E_a,F_b` be the two endpoint binary PVMs
inside a common carrier and define

```text
nu(a,b)=||E_a U F_b||_2^2.                               (SAT7)
```

Orthogonality and completeness of the `F_b` imply

```text
sum_b nu(a,b)=||E_a U||_2^2=tau(E_a),                    (SAT8)
```

while cyclicity of trace gives `sum_a nu(a,b)=tau(F_b)`.  Reusing the
literal endpoint PVM in adjacent contexts gives exact common marginals.
Replacing it by a transported atom changes the marginal by at most `(SAT3)`.
This is precisely the drift term consumed by the robust rank-one floor.
