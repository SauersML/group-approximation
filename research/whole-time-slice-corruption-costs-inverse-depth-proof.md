---
rg: 2
id: whole-time-slice-corruption-costs-inverse-depth-proof
kind: route
title: Count the terms of one layer against the terms of the whole circuit Hamiltonian
target: whole-time-slice-corruption-costs-inverse-depth
requires: []
---

With `c_1 N <= (terms per layer) <= c_2 N` and `D` layers, the total is
`m = Theta(N D)` and one layer's share is

```text
(terms of one layer)/m = Theta(N)/Theta(N D) = Theta(1/D).
```

Take any state which violates every term of one chosen layer maximally and
no other term.  Since `0 <= h_a <= I`, its energy density is at most
`Theta(N)/m = Theta(1/D)`, and it is at least `c/D` for the layer-only
violation.  Scaling the same construction to `k` layers gives density
`Theta(k/D)`, so a budget `epsilon` buys `k = Theta(epsilon D)` fully erased
layers, which is at least one once `epsilon >= c'/D`.

For the second paragraph: a fault-tolerance theorem quantified as "for every
adversary corrupting at most `f(N)` qudits per time step" gives no conclusion
when the adversary corrupts `N > f(N)` qudits at some step.  The parameter
(WTS1) of `bgv-adversarial-fault-tolerance` is `N^(1-o(1))`, and
`N^(1-o(1)) < N` for all large `N`, so the hypothesis fails at the erased
layer.  No stronger reading of that theorem is used here: it is quoted at its
own stated tolerance.
