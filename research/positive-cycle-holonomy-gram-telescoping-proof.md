---
rg: 2
id: positive-cycle-holonomy-gram-telescoping-proof
kind: route
title: Factor the positive kernel into isometries and telescope around the cycle
target: positive-cycle-near-unitary-edges-force-trivial-holonomy
requires: []
---

Positivity and `K_ii=I` give a Gram factorization

```text
K_ij = V_i^* V_j
```

for isometries `V_i:C^d -> H`.  Normalizing Hilbert--Schmidt norm on the
domain, for every edge,

```text
||V_(i+1)-V_i U_i||_2^2
 = 2-2 Re tr_d(U_i^* K_(i,i+1))
 <= 2 ||K_(i,i+1)-U_i||_(2,d)
 = 2 epsilon_i.                                          (PCT1)
```

Right multiplication by subsequent unitaries preserves this norm.  Telescope
`V_0 U_0...U_(m-1)-V_0` by successively replacing `V_i U_i` with
`V_(i+1)`.  The triangle inequality and `(PCT1)` give

```text
||V_0(U_0...U_(m-1)-I)||_2 <= sum_i sqrt(2 epsilon_i).
```

Since `V_0` is an isometry, the left side is exactly the left side of
`(PCH1)`.  If the product is `omega I`, then `(PCH1)` and
`sum_i sqrt(epsilon_i) <= m sqrt(max_i epsilon_i)` give `(PCH2)`.
