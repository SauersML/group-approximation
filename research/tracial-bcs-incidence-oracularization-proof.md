---
rg: 2
id: tracial-bcs-incidence-oracularization-proof
kind: route
title: Use left-right tracial incidence to close the oracularizable source gap
target: oracularizable-tracial-nonru-game-exists
requires:
  - mipstar-bcs-tracial-nonru-exists
  - paddock-slofstra-bcs-forbidden-projection-dictionary
  - fu-mastel-zhang-cc-to-synchronous-cv
---

Let `B` be the Paddock--Slofstra finite BCS, let `A(B)` have tracial
state `tau`, and let `G` be its standard constraint--constraint game.  Write

```text
P_(i,a)=product_(x in U_i) (1+a_x z_x)/2,
E_(x,b)=(1+b z_x)/2.                                      (TO1)
```

Forbidden `P_(i,a)` vanish in `A(B)`, while the allowed atoms form a PVM.
For `x in U_i`, functional calculus in the commuting context gives

```text
P_(i,a) E_(x,b) = 1_(a_x=b) P_(i,a).                      (TO2)
```

Apply the Fu--Mastel--Zhang symmetrized conversion and use the PVM
`(P_(i,a))_a` on constraint question `i` and `(E_(x,b))_b` on variable
question `x`.  Every sampled pair is one of `(i,i),(x,x),(i,x),(x,i)` with
`x in U_i`.  Hence its two PVMs commute, and `(TO2)` makes every incidence
answer consistent.  The correlation

```text
p(a,b | q,r)=tau(P^q_a P^r_b)                             (TO3)
```

is therefore a perfect synchronous tracial strategy and is oracularizable on
every sampled pair.  Equivalently, on `L^2(A(B),tau)`, left and right
multiplication commute and the trace vector realizes `(TO3)`; traciality gives
`L(e)Omega=R(e)Omega` for each measurement projection.

It remains to prove the finite-dimensional gap.  Paddock--Slofstra's
dictionary and the absence of an `R^U` representation give
`omega_qa(G)<1`.  Formula `(FMZ2)` then gives

```text
omega_qa(G^cv)<1.                                         (TO4)
```

Thus `G^cv` simultaneously has a perfect commuting, pairwise-oracularizable
strategy and a fixed finite-dimensional gap.  This avoids the invalid generic
projection of two unrelated contexts: the only mixed questions in `G^cv` are
incidences, exactly where `(TO2)` supplies compatibility.
