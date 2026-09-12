---
rg: 2
id: mark-relative-finite-packet-no-go-proof
kind: route
title: Feed a mark-alive finite representation as a constant ultraproduct
target: mark-relative-finite-packet-decoder-is-impossible
requires:
  - fanizza-turing-bcs-signal-collapse
  - fanizza-reflection-recurrence-has-s4-stationary-overlap
---

Let `rho:Gamma->U(d)` satisfy `rho(p)!=0`.  Repeating `rho` in every
coordinate gives

```text
pi:Gamma -> U(prod_U M_d)
```

with `pi(p)!=0`.  A mark-relative decoder produces a perfect BCS state with
positive `D` mass.  On a Fanizza NONHALT instance, `(FTB1)` at `epsilon=0`
forces that mass to be zero.  Contradiction.  This proves finite-dimensional
invisibility of `p`.

If `Gamma` is finite, its left regular representation is faithful on
`C[Gamma]`, so it detects every nonzero `p`.  If `Gamma` is residually finite,
write `p=sum_(g in F) a_g g` with distinct finite support `F`.  Choose a finite
quotient injective on `F`; the quotient image of `p` is a nonzero linear
combination of distinct basis elements, and its left regular representation
detects it.  Hence in either case a nonzero `p` contradicts the required
decoder.

For the concrete tensor escape, use the exact `S_4` representation from
`fanizza-reflection-recurrence-has-s4-stationary-overlap`, where

```text
u d u^-1=d(x d x^-1),       tr(P xPx^-1)=1/4.
```

Tensor it with any spin representation of `D_8` in which the central Pauli
sign is `-I`.  Words confined to either packet retain their exact values and
the central mark survives, while the stationary overlap is unchanged.  This
refutes every separable finite cell that merely attaches a Pauli mark to the
ordinary reflection recurrence.
