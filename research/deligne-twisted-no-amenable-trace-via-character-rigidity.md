---
rg: 2
id: deligne-twisted-no-amenable-trace-via-character-rigidity
kind: route
title: Cancel conjugate Maslov multipliers and force an amenable regular trace
target: deligne-twisted-fibres-have-no-amenable-trace
requires:
  - deligne-maslov-sector-traces-are-central-regular
---

Let `Z=Z(E_3)` and

```text
Ebar=E_3/Z ~= PSp_4(Z).
```

The trace-classification theorem expresses every trace on `A_omega` as

```text
t tau_(eta_+) +(1-t)tau_(eta_-).
```

If such a trace were amenable, amenability would pass to every nonzero
central cut.  Hence at least one full-central-character trace `tau_eta`
would be amenable.  Complex conjugation makes `tau_(bar eta)` amenable, and
tensor products preserve amenability.

In `A_eta tensor_min A_(bar eta)`, the unitaries

```text
v_(gbar)=u_g^eta tensor u_g^(bar eta)
```

form an ordinary representation of `Ebar`: changing the lift `g` multiplies
the two factors by inverse central scalars, and the two Maslov multipliers
cancel.  The tensor trace restricts to

```text
tr(v_(gbar))=delta_(gbar,1).
```

Thus the canonical trace of `C^*(Ebar)` would be amenable.  The canonical
group trace is amenable exactly when the group is amenable, but
`PSp_4(Z)` is nonamenable.  This contradiction proves that neither twisted
fibre has an amenable trace.

This proof uses character rigidity, central cuts, and nonamenability only;
it invokes no Property `(T)`, Kazhdan projection, or Kazhdan transport.
