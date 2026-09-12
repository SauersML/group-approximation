---
rg: 2
id: parity-majority-involution-proves-central-norm-conjugacy
kind: route
title: Separate cyclic parity, cancel the quadratic offset, and encode matrix coefficients in finite central blocks
target: central-odd-norm-quadratic-ca-are-conjugate-to-linear
requires: []
artifacts:
  - research/artifacts/gottschalk-central-odd-norm-conjugacy-direct-finiteness-2026-09-08.md
---

Since n is odd, E^2=E. Write x=d+c with Ed=0 and c=Ex, and put
h(d)=E Q_t(d). Expanding the quadratic term gives

    E Q_t(c+d)=c+h(d),

because the mixed term has zero cyclic norm. Thus Psi acts as
(d,c)->(d,c+h(d)), an involution. In these coordinates F_B is
(d,c)->(d,Bc+(B-I)h(d)); conjugating by Psi leaves (d,Bc).
The same conjugacy for every B proves the multiplication identity.

For n=3, Psi swaps each weight-one triple with its weight-two
complement and fixes 000 and 111, changing cyclic parity to majority.
Scalar linear duality identifies B_b with the dual of right
multiplication by b on F_2[Gamma], proving the stated direct-finiteness
equivalence with all inverse orientations explicit.

For matrix rules, the central idempotent e=a+a^2 in F_2[S_3] has
block M_2(F_2). Tensor powers give M_(2^k)(F_2). Pad the matrix rule,
embed its coefficients in this block, and put identity on the
complement. A finite track change identifies the scalar rule with
copies of the original rule and identity tracks. Apply the proved
central three-cycle conjugacy. Every claim is over F_2.
