---
rg: 2
id: universal-relations-cannot-force-proper-infiniteness-proof
kind: route
title: The left regular representation is always available and carries a faithful trace
target: universal-relations-cannot-force-proper-infiniteness
requires: []
---

Suppose the relations `R` forced the image of `p` to be nonzero and properly
infinite in every unitary representation of `G`. The left regular
representation

```text
lambda : G -> U(l^2 G)
```

is a unitary representation of `G` -- it satisfies `R`, since `G` does -- so
the hypothesis applies to it. Write `q = lambda(p) in C*_r(G)`, a nonzero
properly infinite projection.

`C*_r(G)` carries the canonical tracial state

```text
tau(a) = <a delta_e, delta_e>,
```

which is a **faithful** trace on `C*_r(G)`: `tau(a^* a) = ||a delta_e||^2`,
and `a delta_e = 0` forces `a lambda(g) delta_e = lambda(g) a delta_e = 0`
for all `g` when `a` commutes appropriately -- more directly,
`a delta_e = 0` gives `<a delta_g, delta_h> = <a delta_e, delta_(h g^-1)> = 0`
for all `g,h`, hence `a = 0`.

Proper infiniteness of `q` means `q ⊕ q` is Murray--von Neumann subequivalent
to `q` inside `M_2(C*_r(G))`. Applying the (unnormalized) trace
`tau ⊗ Tr_2` to that subequivalence gives

```text
tau(q) + tau(q)  <=  tau(q),
```

so `tau(q) <= 0`. Since `tau` is a state, `tau(q) >= 0`, hence `tau(q)=0`,
and faithfulness gives `q = 0` -- contradicting nonzeroness.

The argument uses nothing about `G` beyond the existence of `lambda`, which
is why it closes the whole family of shortcuts at once. It is also exactly
why a Kazhdan-corner variant fails: whatever the complement of a Kazhdan
projection is asked to do, `lambda` sends it to `1`, and `tau(1)=1` with `1`
finite.
