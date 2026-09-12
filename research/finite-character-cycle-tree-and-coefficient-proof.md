---
rg: 2
id: finite-character-cycle-tree-and-coefficient-proof
kind: route
title: Reduce partial transports along a tree and compare finite-character coset coefficients
target: finite-character-rotation-cycles-have-exact-loop-algebra
requires:
  - finite-augmentation-corner-has-outside-normalizer-contexts
  - lin-explicit-fixed-bcs-gap-via-generic-conversion
artifacts:
  - research/artifacts/finite-character-partial-rotation-cycle-algebra-2026-09-08.md
---

The tree partials `u_i=h_i f_0` give matrix units `u_i u_j^*`.
Each remaining edge has root entry `f_0 ell_e`. Equality of finite-
character projections forces equality of their subgroup supports and
characters, so all `ell_e` normalize `H_0` and preserve `chi_0`.
These entries generate exactly `f_0 C[L]f_0`; multiplication by the
tree matrix units proves the claimed full algebra isomorphism.

Distinct `H_0`-cosets have disjoint Fourier supports. Choosing coset
representatives therefore gives a basis with the stated finite-phase
cocycle, and exact equality is coefficient equality in that basis.
The partial-rotation identity used in the two-context construction
keeps arbitrary additive products inside this matrix algebra on `p`,
with a scalar summand on any leftover augmentation corner `q-p`.

Expanding `e_K e_(H,chi)` coefficientwise gives the character
sum over `K intersect H`. Its vanishing proves the stated
augmentation-containment criterion. Taking canonical traces gives
the exhaustion arithmetic, and the faithful trace makes it sufficient
once orthogonality and containment have been established.

For the triangle, multiplication by the initial and final projections
recovers `a/2` or `b/2` from the rotated projection. Their equality is
therefore equivalent to `a^*b=w f_0=f_0`. Supports and character
coefficients identify this with `w in ker chi_0`. Expanding the squared
HS difference gives `tau(f_0)-Re tau(w f_0)`, hence the exact trace
formula.

Scalar fundamental returns make `L=H_0`; a finite quotient gives a
finite-dimensional algebra. A scalar leftover gives a scalar quotient.
For hyperlinear `L`, finite-corner normalization and matrix amplification
preserve its CE canonical trace. Each alternative contradicts a unital
map from the fixed no-CE BCS. The argument imposes no relation that
would close a still-open return word or authenticate a new group quotient.
