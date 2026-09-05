---
rg: 2
id: stw99-lxxvi-exact-positive-cutoff-restriction-proof
kind: route
title: The CAR diagonal expectation obstructs extension of an oscillatory cutoff frame
target: stw99-lxxvi-exact-positive-cutoff-restriction-not-onto
requires: []
artifacts:
  - research/artifacts/stw99-lxxvi-hereditary-k-stability-and-cutoff-restriction-2026-09-05.md
---

In the tensor diagonal Delta=C({0,1}^N), put c=sum 2^(-n)e_n,
a=(c-1/4)_+, b=(c-1/2)_+, and
h(t)=sqrt((t-1/2)_+/(t-1/4)_+), extended by zero below 1/4.
A frame w with w*w=a represents T_w(a^(1/2)x)=wx. Its actual
restriction is represented by w h(c), since b^(1/2)=a^(1/2)h(c).

The continuous diagonal frame
v(t)=sqrt(t-1/2) exp(i/(t-1/2)) above 1/2, zero below, satisfies
v*v=b. If w h(c)=v, the diagonal conditional expectation would force
E(w)(omega)=sqrt(c(omega)-1/4) exp(i/(c(omega)-1/2)) above 1/2.
Binary tails attaining 1/2+1/(2 pi n) and 1/2+1/(2 pi n+pi)
both converge to (1,0,...), but these forced values tend to 1/2
and -1/2. This contradicts continuity of E(w). Indeed no element
w of A, even without w*w=a, solves the restriction equation.

The nonzero diagonal projection e=(1-e_1)(1-e_2) annihilates a,
so [a]<=[1-e]<[1]. In the stabilization a frame with initial
positive a and target projection 1_A must still lie in the fixed
A corner. Matrix coordinates therefore do not evade the obstruction.
