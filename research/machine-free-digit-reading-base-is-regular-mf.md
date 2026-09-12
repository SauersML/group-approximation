---
rg: 2
id: machine-free-digit-reading-base-is-regular-mf
kind: claim
title: The p-free digit-reading HNN base is regularly operator-MF
distinct_from:
  machine-free-digit-reading-group-is-mf: that adds the final p-HNN edge sending t to td while centralizing every a_i; this proves regular MF only before that edge.
  modular-machine-boone-group-is-mf: that treats the machine instruction tower; this treats the independent digit endomorphisms on the x,t,b,d free base.
---

Fix `m>=3`, put

```text
F=<x,t>*F(b_1,...,b_s,d),
phi_i(x)=x^m,   phi_i(t)=x^-i t x^i,
phi_i(b_j)=b_j, phi_i(d)=b_i d,
```

and form the multiple ascending HNN extension

```text
Gamma'=<F,a_1,...,a_s | a_i f a_i^-1=phi_i(f), f in F>.
```

Then `Gamma'` has a regular operator-MF realization.  In particular it is
operator-MF.  Thus the unresolved part of the machine-free digit reader is
only its final `p`-edge, not the digit endomorphism tower itself.
