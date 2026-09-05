---
rg: 2
id: stw99-l-tensor-square-actions-give-k0-k1-block
kind: claim
title: The two tensor-factor circle actions on B tensor B are a basis of the Hom(K0 mod unit, K1) block
artifacts:
  - research/artifacts/stw99-l-six-kirchberg-loops-2026-09-05.md
---

Let `A = B (x) B` (minimal tensor product), a unital UCT Kirchberg
algebra.  Kunneth gives bases

```text
K_0(A) = Z e (+) Z beta,   e = e_B [x] e_B = [1_A],   beta = v [x] v
K_1(A) = Z x (+) Z y,      x = v [x] e_B,             y = e_B [x] v
```

so `A` has scaled graded K-theory `(Z^2, (1,0), Z^2)`.  The two circle
actions

```text
rho_1(z) = gamma_z (x) id_B,      rho_2(z) = id_B (x) gamma_z
```

have invariants

| loop | Delta(x) | Delta(y) | Delta(beta) | Delta(e) |
| --- | --- | --- | --- | --- |
| rho_1 | e | 0 | y | 0 |
| rho_2 | 0 | e | -x | 0 |

The MINUS SIGN is not a convention: it is the Koszul sign of the graded
external product, from moving the odd suspension class past the odd class
`v`.  In particular `(Delta_{rho_1}(beta), Delta_{rho_2}(beta)) = (y,-x)`
is a `Z`-basis of `Hom(K_0(A)/Z[1_A], K_1(A)) = Z^2`.
