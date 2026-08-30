---
rg: 2
id: waldhausen-free-double-whitehead-space-proof
kind: route
title: Put the free double in Waldhausen's class Cl
target: waldhausen-free-double-whitehead-space-contractible
requires: []
---

Use Waldhausen, Algebraic K-theory of generalized free products, Part 2,
Annals of Mathematics 108 (1978), 205--256,
DOI 10.2307/1971166.

Finite-rank free groups are regular coherent and belong to Waldhausen's
class Cl. Theorem 19.1(iv) says that every subgroup of a regular coherent
group is regular coherent, so the arbitrary subgroup R <= F is regular
coherent even when it is infinitely generated. Definition 19.2(3), the
closure of Cl under amalgamation over a regular coherent subgroup, therefore
puts

    L = F *_R F

in Cl. Since Z is regular noetherian, Theorem 19.4 applies and makes the
entire Whitehead space Wh_Z(L) contractible. Proposition 15.7 identifies its
based fundamental group with the ordinary Whitehead group, giving Wh(L)=0.
QED

The point of using Theorem 19.1(iv) is precisely that no hidden
finite-generation hypothesis on R enters the argument.
