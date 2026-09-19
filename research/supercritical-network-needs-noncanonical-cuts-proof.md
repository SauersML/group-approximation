---
rg: 2
id: supercritical-network-needs-noncanonical-cuts-proof
kind: route
title: Run the pressure inequality in the exact model and evaluate the flat table
target: supercritical-network-needs-noncanonical-cuts
requires:
  - fractional-source-branch-pressure
  - soft-block-mass-yields-fractional-branch
  - pauli-two-child-transfer-packet
---

**`(NCC1)`.**  A canonical network is by definition defined in the exact model
too, and `fractional-source-branch-pressure` is a theorem about an arbitrary
finite tracial von Neumann algebra, so `(FSB1)` and `(FSB3)` hold there with the
limit data.  Canonicity gives `eta^inf = lim eta^(n) = 0`, whence
`kappa(y . x^inf) <= 0`.  With `y>0` and every `x_i^inf >= 0` this forces
`x^inf = 0` on the component.  `pauli-two-child-transfer-packet` supplies a
state of exact trace `1/8` on the component that carries the genuine branch,
which is the contradiction.  `(NCC2)` is the contrapositive.

**`(NCC3)`.**  Apply `soft-block-mass-yields-fractional-branch` with
`P=F_eps`, `Q=G_eta`, `W=1`, `X=G_eta F_eps`.  Then

```text
||X||_2^2 = tau(F_eps G_eta G_eta F_eps) = tau(F_eps G_eta) = 1/64,
x = tau(F_eps) = 1/8,
```

so `(SBM1)` gives `tau(E_t) >= (1/64 - t^2/8)/(1-t^2)` and the coverage
fraction is

```text
c_eta(t) = tau(E_t)/tau(F_eps) >= (1/8 - t^2)/(1 - t^2).
```

The function `u |-> (1/8-u)/(1-u)` has derivative `(1/8-1)/(1-u)^2 < 0`, so it
is decreasing in `u=t^2` and maximal at `t=0` with value `1/8`.  Summing the
four targets gives the bound `1/2`, attained only in the limit `t -> 0`, and
positivity requires `t^2<1/8`.

For the ceiling, `(SBM2)` gives `tau(E_t) <= (1/64)/t^2`, hence
`c_eta(t) <= 1/(8t^2)` and `sum_eta c_eta(t) <= 1/(2t^2)`, which is at most `1`
exactly when `t^2 >= 1/2`.

Both computations use only the exact rational masses of
`TRUE_DOUBLE_PAULI_COMB_IS_FOURIER_FLAT.md`, which are established by exact
group-algebra arithmetic over the binary Leavitt-prefix model.
