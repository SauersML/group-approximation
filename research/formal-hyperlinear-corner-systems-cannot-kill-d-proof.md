---
rg: 2
id: formal-hyperlinear-corner-systems-cannot-kill-d-proof
kind: route
title: Apply hyperlinear Kervaire-Laudenbach to the virtually free formal coefficient group
target: formal-hyperlinear-corner-systems-cannot-kill-d
requires:
  - kervaire-laudenbach-holds-for-hyperlinear
  - leavitt-two-relator-corner-peeling
---

Both `V4` and `D8` are finite.  Their free product with a finite-rank free group is
virtually free (equivalently, it is the fundamental group of a finite graph
of finite groups after adding free loops), hence residually finite.  Thus
`D*F` is sofic and therefore hyperlinear.

Nitsche--Thom's theorem recorded in
`kervaire-laudenbach-holds-for-hyperlinear` says that every nonsingular
one-variable equation over a hyperlinear coefficient group injects that
coefficient group into the relative quotient.  The exponent of the cyclic
word is its cover degree and is nonzero.  Applying the theorem to `D*F`
shows that `h`, which is nonidentity in the `D8` factor, cannot die.

This argument does not forbid using formal incidence as a design language.
It forbids promoting such a design to a proof while its corner subgroup is
still `D*F`.  The promotion must demonstrate a Leavitt-specific corner
relation and audit its effect on the coefficient embedding.
