---
rg: 2
id: reverse-kleene-tensor-power-firewall-proof
kind: route
title: Tensor powers amplify every nontrivial unitary past a cutoff below square-root two
target: reverse-kleene-unconditioned-collapse-forces-fd-invisibility
requires: []
---

Let `V=pi(w)` in an exact finite-dimensional representation and put
`z=tr(V)`.  If `|z|<1`, then the exact tensor-power representations satisfy

```text
||pi^(tensor k)(w)-I||_2^2 = 2-2 Re(z^k) -> 2,
```

contradicting `(RKF1)` for large `k`.  If `|z|=1`, equality in the triangle
inequality makes `V=lambda I`; when `lambda!=1`, some power has
`Re(lambda^k)<=0` and again reaches distance at least `sqrt(2)`.  Thus
`V=I`.

For a homomorphism into a tracial matrix ultraproduct, apply the same argument
to its image of `w` and represent each fixed tensor power coordinatewise.
Every fixed relator defect still tends to zero, so `(RKF1)` gives the same
contradiction unless the ultraproduct image of `w` is `1`.
