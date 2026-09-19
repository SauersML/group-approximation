---
rg: 2
id: normalized-hs-taylor-remainder-is-not-dimension-free-proof
kind: route
title: Differentiate a word twice and evaluate on a rank-one anti-Hermitian direction
target: normalized-hs-taylor-remainder-is-not-dimension-free
requires: []
---

Differentiating `t -> U_1(t) ... U_k(t)` twice at `t = 0` by the product
rule gives a finite sum of terms `A X_i B X_j C` (each factor `A, B, C` a
product of the `U`'s) plus terms `A X_i^2 B`; all are of the displayed
form.  For any matrices, `|| A X B Y C ||_2 <= || A ||_op || X ||_op || B ||_op || Y ||_2 || C ||_op`,
and unitaries have operator norm one, which is `(NHT1)` with `L` the number
of terms.

For `F(U) = U^2`, `U(t) = exp(tX)`, `F(U(t)) = exp(2tX)` and
`F''[X, X] = 4 X^2`.  Take `X = i pi . e e^*` for a unit vector `e`.  Then
`X^2 = -pi^2 e e^*`, `Tr |X|^2 = pi^2`, `Tr |X^2|^2 = pi^4`, so with the
normalized trace `|| X ||_2^2 = pi^2 / d` and `|| X^2 ||_2^2 = pi^4 / d`, giving
`(NHT2)`.  Any inequality `|| F''[X,X] ||_2 <= L' || X ||_2^2` would force
`4 pi^2 / sqrt d <= L' pi^2 / d`, i.e. `L' >= 4 sqrt d`.

Inside the Iwahori setting the same `X` is a tangent vector to the unitary
group at a modular vertex representation that rotates a single eigenline by
the angle `pi` and leaves every eigenvalue multiplicity unchanged, so it
lies in a fixed torsion-multiplicity stratum; its normalized-HS length is
`pi / sqrt d` while its operator norm is `pi`.  This is the rank-one
phenomenon named in the claim.
