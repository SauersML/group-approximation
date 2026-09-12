---
rg: 2
id: finite-bass-serre-selector-countermodel-proof
kind: route
title: Separate the marked packets in one finite quotient of the Bass--Serre group
target: finite-bs-selectors-have-marked-fd-countermodels
requires: []
---

The base `(FBS1)` is `C_2` times a right-angled Coxeter group, hence is
residually finite.  The finite-edge Bass--Serre residual-finiteness theorem,
applied inductively, preserves residual finiteness under every listed
amalgam and HNN extension.  The selector packet `(FBS3)` is finite because
the relations reduce every word to `c p^epsilon q^delta`; the usual central
two-cocycle multiplication on `C times F_2^2` realizes the presentation and
keeps `C` embedded.

There are only finitely many nonidentity elements in the union of the named
packets.  Separate each of them in a finite quotient and take the diagonal
map to the product of those quotients.  It is injective on every packet and
does not kill `J`.  Restriction of the regular representation of the finite
target to an injected packet is a multiple of that packet's regular
representation, which gives `(FBS4)` and the exact marked finite
countermodel.
