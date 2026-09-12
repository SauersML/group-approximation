---
rg: 2
id: integral-jacobson-centerless-quotient-carries-dichotomy-proof
kind: route
title: Compute the centralizer of the finitary transvections, push the restricted dichotomy through it, and use the order-two central quotient lemma for the converse
target: integral-jacobson-centerless-quotient-carries-dichotomy
requires:
  - integral-jacobson-mf-radical-is-all-or-nothing
  - mf-group-with-order-two-center-has-mf-central-quotient
  - integral-jacobson-sign-quotient-is-residually-finite
artifacts:
  - research/artifacts/jacobson-exact-torsion-radical-and-integral-dichotomy-2026-09-09.md
---

## Why sufficient

**Centralizer.**  `G_n` acts faithfully on `V = Z^(({1..n}) x N_0)` and
`N_n` contains every finitary transvection `I + E_(ab)`, `a != b`.  If
`X` commutes with all of them, then applying `X E_(ab) = E_(ab) X` to
`e_c` for `c != b` shows that the `b`-coefficient of `X e_c` vanishes,
so `X` is diagonal, and applying it to `e_b` equates the `a`- and
`b`-coefficients, so `X = lambda I`; integrality of `X` and `X^-1` gives
`lambda = +-1`.  The matrix `-I` lies in `G_n` for even `n` as the
product of the `w_(ij)^2 = diag(.., -1, .., -1, ..)` over disjoint pairs,
and not for odd `n` since `EL_n(S)` has determinant one.  It is not
finitary.  Hence `C_(G_n)(N_n) = Z(G_n) = G_n cap {+-I}` and
`Z(G_n) cap N_n = 1`.

**(CZ1).**  By the first prerequisite either `N_n <= ker(phi)` or
`ker(phi) cap N_n = 1`.  In the second case, for `x in ker(phi)` and
`n in N_n`, `[x, n] in ker(phi) cap N_n = 1`, so `x in C_(G_n)(N_n) =
Z(G_n)`.  For odd `n` this is `x = 1`.

**`P_n` for even `n`.**  If `g{+-I}` centralizes the image of `N_n` in
`P_n`, then `[g, n] in {+-I} cap N_n = 1` for all `n in N_n`, so
`g in Z(G_n) = {+-I}`; thus `C_(P_n)(N_n{+-I}/{+-I}) = 1`.  An MF-valued
homomorphism `psi` of `P_n` composed with `G_n -> P_n` is an MF-valued
homomorphism of `G_n`, so by (CZ1) either it kills `N_n`, i.e. `psi`
kills the image of `N_n`, or its kernel is contained in `{+-I}`, i.e.
`psi` is injective.

**(CZ2).**  If `G_n` is MF, its center is the single involution `-I`,
so the second prerequisite makes `P_n` MF.  If `P_n` is MF, then
`G_n -> P_n x T_n`, `g -> (g{+-I}, gN_n)`, has kernel `{+-I} cap N_n = 1`,
and `T_n` is MF by the third prerequisite, so `G_n` embeds in a product
of MF groups and is MF.
