---
rg: 2
id: stable-steinberg-cover-kills-clock-shift-multiplier-proof
kind: proof
title: Vanishing K-two of F2 makes every large binary projective representation linear
target: binary-gl-finite-sections-have-no-projective-k2-phase
requires:
  - toeplitz-folner-compressions-cannot-retain-jacobson-head
---

## The universal central extension

Because `F_2^times={1}`,

```text
GL_m(F_2)=SL_m(F_2)=E_m(F_2).                           (SKP1)
```

For `m>=5` this group is perfect, and the Steinberg map

```text
St_m(F_2)->E_m(F_2)                                     (SKP2)
```

is its universal central extension. Its kernel is the unstable group
`K_2(m,F_2)). Field stability identifies this kernel with stable
`K_2(F_2)).

Quillen's calculation of the algebraic K-theory of finite fields gives

```text
K_2(F_q)=0
```

for every finite field. Therefore `K_2(m,F_2)=0), so the universal
central extension `(SKP2)` is already an isomorphism. Equivalently,

```text
H_2(GL_m(F_2),Z)=0                                      (SKP3)
```

for `m>=5`. Our dimensions `m=28N` are safely in this range.

This also agrees with the explicit finite-group computation: the Schur
multiplier of `GL_m(F_p)` is trivial outside the exceptional pairs
`(m,p)=(3,2),(4,2)`. See Erfanian--Rezaei--Jafari, *Computing the
non-abelian tensor square of general linear groups*, Ital. J. Pure Appl.
Math. 24 (2008), 203--210; the result is quoted explicitly in the
introduction of Jezernik, arXiv:1305.4055.

## Consequence for projective representations

For a finite perfect group `G`, the universal-coefficient sequence and
divisibility of `U(1)` identify projective multiplier classes with

```text
H^2(G,U(1)) isomorphic to Hom(H_2(G,Z),U(1)).            (SKP4)
```

Equations `(SKP3)--(SKP4)` prove `(BGP2)`. Hence for every projective
unitary representation `pi` of `GL_(28N)(F_2)` there is a scalar
function `a(g) in U(1)` such that

```text
rho(g)=a(g)pi(g)
```

is an ordinary unitary representation.

In the ordinary representation `rho), conjugate group elements have
unitarily conjugate images. The boundary transvection and head
transvection in the finite-section proof are conjugate, so no central
element of a covering group can distinguish them.

A different choice of representatives for the same projective
representation replaces `rho(g)` by arbitrary scalar factors
`a(g)^(-1)`. Those factors form a one-cochain, not a nonzero class in
`H^2`. They may change the phase of an evaluated word, but they receive
no consistency for free from projective representation theory. In
particular, using them in a microstate requires a separate check of every
fixed presentation relator.

This is why the usual Heisenberg clock-shift repair has no analogue here.
Clock-shift sectors exploit a nontrivial central extension. The finite
binary general-linear host has none in dimensions `28N). The only
remaining phase route is a deliberately relator-dependent scalar
perturbation, not a Schur or K-two multiplier.
