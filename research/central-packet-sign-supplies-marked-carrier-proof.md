---
rg: 2
id: central-packet-sign-supplies-marked-carrier-proof
kind: route
title: Round the almost involution and use centrality to reduce its negative corner
target: central-packet-sign-supplies-marked-carrier
requires:
  - marked-hs-separation-forces-spectral-density
---

Since `W` is unitary,

```text
||W-W^*||_2=||W^2-I||_2<=sqrt(E).
```

Put `H=(W+W^*)/2`.  Then `||W-H||_2<=sqrt(E)/2`.  Functional calculus rounds
`H` to its sign `Z`.  On `[-1,1]`, distance to the nearest sign is bounded by
`|1-t^2|`; telescoping `H^2-W^2` therefore gives the safe fixed estimate
`||H-Z||_2<=2sqrt(E)`, proving `(CSM1)`.

For an involution, `||Z-I||_2^2=4tau(Q)`.  The triangle inequality and
`sqrt(E)<=alpha/6` give `||Z-I||_2>=alpha/2`, which is `(CSM2)`.

Finally, approximate centrality and `(CSM1)` give

```text
||[Z,U(s)]||_2
 <= ||[W,U(s)]||_2+2||Z-W||_2
 <= 7sqrt(E).
```

Division by two in `Q=(I-Z)/2` yields `(CSM3)`.  The exact representation
with `pi(J)=-I` proves nontriviality of the marked group element independently
of any finite-dimensional approximation.
