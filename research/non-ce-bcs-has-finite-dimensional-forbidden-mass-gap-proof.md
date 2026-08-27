---
rg: 2
id: non-ce-bcs-has-finite-dimensional-forbidden-mass-gap-proof
kind: route
title: Tracial matrix ultraproduct kills a vanishing forbidden mass
target: non-ce-bcs-has-finite-dimensional-forbidden-mass-gap
requires:
  - mipstar-bcs-tracial-nonru-exists
---

Suppose no such `beta_B` exists.  Then there are dimensions `d_n` and tuples
`Z^(n) = (Z_x^(n))` of self-adjoint involutions in `M_(d_n)(C)`, commuting
exactly within each context, whose left side in `(FMG)` tends to zero.

Form the tracial matrix ultraproduct `prod_omega (M_(d_n)(C), tau_(d_n))` for a
free ultrafilter `omega`, and let `Z_x = [Z_x^(n)]_omega`.  Each `Z_x` is a
self-adjoint involution, and for `x, y` in a common context the commutator
vanishes at every stage, hence vanishes in the ultraproduct.  So the joint
spectral projections

```text
P_a^c = prod_(x in U_c) (I + (-1)^(a_x) Z_x)/2
```

are genuine projections in the ultraproduct for every context `c` and
assignment `a` on `U_c`.

For each forbidden `a in F_c` the corresponding trace is a nonnegative term of a
sum tending to zero, so it tends to zero, and the ultraproduct trace of `P_a^c`
is `0`.  The ultraproduct trace is faithful, so `P_a^c = 0`.

Therefore the assignment `Z_x` satisfies every defining relation of the BCS
algebra of `B` -- contextwise commutation exactly, and vanishing of every
forbidden joint spectral projection -- and so determines a unital
`*`-homomorphism from that algebra into the ultraproduct.  Composing with the
ultraproduct trace gives a tracial state on the BCS algebra whose GNS algebra
embeds in the ultraproduct.

A tracial matrix ultraproduct embeds trace-preservingly into `R^omega`, so that
tracial state is Connes-embeddable, contradicting the hypothesis on `B`.

Existence of a `B` with the hypothesis is `mipstar-bcs-tracial-nonru-exists`,
which records Paddock--Slofstra Example 4.2: a finite BCS whose synchronous
algebra has a tracial state but no homomorphism to `R^U`.  Those two properties
are the same hypothesis, since a tracial state pulled back along a unital
homomorphism into `R^U` is Connes-embeddable and conversely the GNS
representation of a Connes-embeddable tracial state is such a homomorphism.
