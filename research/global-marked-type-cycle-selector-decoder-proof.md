---
rg: 2
id: global-marked-type-cycle-selector-decoder-proof
kind: route
title: Sum selector-cycle pressure through the finite marked-type packet
target: global-marked-type-cycle-selector-decoder
requires:
  - cyclic-coarse-fine-selector-rows-spread-carrier-error
---

Decompose the permutation `sigma` of the finite set `Omega` into disjoint
cycles.  On each cycle apply
`cyclic-coarse-fine-selector-rows-spread-carrier-error` with
`a=1/2`, `b=1/4`.  Summing the cycle inequalities gives

```text
sum_omega d_omega^2 >= (1/4) sum_omega tr(P_omega).    (GTP1)
```

The assumed coverage estimate `(GTC5)` therefore yields

```text
sum_omega d_omega^2
 >= (alpha/4) E_forbid(U)-zeta(delta)/4.                (GTP2)
```

On the other hand `(GTC4)`, followed by `(GTC1')` separately for every word
`r in T`, gives

```text
sum_omega d_omega^2
 <= K sum_(r in T) sum_omega ||(r(U)-1)Q_omega||_2^2
      +eta(delta)
 <= KL sum_(r in T)||r(U)-1||_2^2+eta(delta).           (GTP3)
```

Combining `(GTP2)` and `(GTP3)` and rearranging gives exactly

```text
sum_(r in T)||r(U)-1||_2^2
 >= alpha/(4KL) E_forbid(U)
    -(eta(delta)+zeta(delta)/4)/(KL),
```

which is `(GTC6)`.

For the global non-CE endpoint, combine this with the fixed ordinary-energy
bound for `E_base` and the robust BCS floor
`E_base+E_forbid>=beta_B^rob`.  If `E_base>=beta_B^rob/2`, the base rows pay a
fixed presentation-energy floor.  Otherwise
`E_forbid>=beta_B^rob/2`, and `(GTC6)` pays a fixed floor for the actuator
menu once the vanishing moduli are small enough.  Thus the criterion has the
claimed dimension-independent consequence without selecting a preferred
context, type, or carrier cycle.