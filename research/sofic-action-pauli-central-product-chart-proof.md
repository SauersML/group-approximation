---
rg: 2
id: sofic-action-pauli-central-product-chart-proof
kind: route
title: Replicate the Pauli center over all carriers of a sofic action chart
target: sofic-action-gives-marked-pauli-central-product-microstates
requires:
  - gkp-sofic-action-is-liftable-hamming-chart-family
artifacts:
  - research/artifacts/sofic-action-pauli-central-product-microstates-2026-08-30.md
---

Fix a finite multiplication window in `P_X semidirect A`, and let `E` be
the union of all Pauli supports and all actor-translates of those supports
which occur in the window.  For `eta>0`, a sofic action chart gives a finite
carrier `Omega`, almost-multiplicative permutations `sigma_a`, and labels

```text
ell_x:Omega->L,       x in E,                             (PCP1)
```

such that distinct labels collide on at most an `eta`-fraction of carriers
and

```text
ell_(ax)(sigma_a omega)=ell_x(omega)                      (PCP2)
```

off another `eta`-fraction for every required pair `(a,x)`.  A union bound
makes `x |-> ell_x(omega)` injective on `E` and makes all required covariance
equations simultaneous outside `O_E,A(eta)` of the carriers.  Product this
chart with an independent free sofic approximation of `A`; this preserves
the label statistics and separates actor words.

On each carrier put the finite group

```text
P_L=F_2^(L) x F_2^(L) x F_2
```

with cocycle `<v,u'>`, and form the finite wreath group

```text
Q=P_L^Omega semidirect Sym(Omega).                        (PCP3)
```

For `p=(u,v,e)` define its base function at `omega` by pushing both supports
through `x |-> ell_x(omega)` and retaining the same central bit `e`.  On an
injective carrier, push-forward preserves the dot product, so it preserves
the Pauli cocycle exactly.  Equation `(PCP2)` gives exact semidirect
covariance on every good carrier.  Hence every requested multiplication
equation fails on only `O_E,A(eta)` of the carriers.

Use the imprimitive action of `(PCP3)` on `P_L x Omega`, with every base
group acting left-regularly in its fibre.  A nontrivial Pauli word acts
without fixed points on every injective carrier; a nontrivial actor moves
almost every fibre.  Most importantly, the common source mark maps to

```text
omega |-> J_L,                                            (PCP4)
```

which moves every point of every fibre.  Letting `eta` tend to zero proves
soficity and keeps the mark at Hamming distance one.

For the two-point quotient, write `X(u)=(u,0,0)` and `Z(v)=(0,v,0)`.  The
normal form gives `J!=1` and

```text
[X(delta_p+delta_q),Z(delta_p)]=J.                        (PCP5)
```

Transitivity makes the actor conjugates of `Z(delta_p)` generate the second
Pauli coordinate, proving the marked surjection asserted in the target.
The complete finite-window estimates and the comparison with the nearby
halo, exact-atlas, and moving-character no-go results are in the artifact.

