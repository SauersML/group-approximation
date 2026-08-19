---
rg: 2
id: atlas-a4-packet-centralizer-product-compiler-proof
kind: route
title: Apply A4 centralizer-product rounding to the finite packet one context at a time
target: atlas-a4-packet-centralizer-product-compiler
requires:
  - atlas-shortest-a4-triangle-packet
  - a4-near-context-centralizer-product-rounding
---

Restriction of `Reg(A8)` to any A4 subgroup is

```text
[A8:A4] Reg(A4) = 1680 Reg(A4),
```

so every order-three/order-two pair in the thirty-word packet has exactly the
regular A4 margin required by `a4-near-context-centralizer-product-rounding`,
with multiplicity `1680 k_n`.

For a word `(b_2 a_1)^3`, the represented defect is

```text
||(U rho(b) U^* rho(a))^3-1||_2,
```

so the rounding theorem gives

```text
dist_2(U, U(rho(<a>)') U(rho(<b>)')) -> 0.
```

For a factor-reversed word `(b_1 a_2)^3`, conjugate the word by `U^*`.
The resulting defect has the same normalized-HS norm and the form required by
the local theorem with relative unitary `U^*`.  Taking adjoints converts its
conclusion into

```text
dist_2(U, U(rho(<b>)') U(rho(<a>)')) -> 0.
```

There are exactly thirty contexts, independent of `n`.  Taking the maximum of
the thirty quantities preserves convergence to zero and proves
`(A4-PACKET-CENT)`.
