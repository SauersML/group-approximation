---
rg: 2
id: dyadic-perturbation-radical-proof
kind: route
title: Kill a three-cycle by the commuting-conjugate criterion and bound the radical by the parity quotient
target: dyadic-perturbation-group-mf-radical-is-finitary-alternating
requires:
  - dyadic-finite-perturbation-group-elementary-structure
  - dyadic-perturbation-group-has-three-point-commuting-witness
  - affine-semidirect-sl3-source-has-property-t
  - locally-finite-centralizer-derived-subgroup-is-mf-invisible
artifacts:
  - research/artifacts/dyadic-finite-perturbation-sofic-non-mf-2026-09-08.md
---

## The lower bound: a three-cycle dies

The second prerequisite supplies `L = Gamma`, `u = a^3`, `ell = t_(e_1)`
and `C = Sym{x_0,x_1,x_2} = S_3` with `C <= C_G(Gamma)` locally finite,
`u Gamma u^-1 <= Gamma`, and
`[uCu^-1, ell u C u^-1 ell^-1] = 1`.  The third supplies property (T) for
`Gamma`.  These are the four hypotheses of the fourth prerequisite, which
therefore kills `[C,C] = A_3` in every norm-corona homomorphism, hence in
every homomorphism to an MF group.

Every three-cycle of `Sym_fin(X)` is conjugate, by a finitely supported
permutation, to one supported on `{x_0,x_1,x_2}`, so every three-cycle
dies.  Three-cycles generate `Alt_fin(X)`: write an even permutation as
an even number of transpositions and pair them; a pair sharing a letter
is a three-cycle, and for four distinct letters
`(ab)(cd) = (acb)(acd)`.  Hence

```text
Alt_fin(X) <= Rad_MF(G),                                          (1)
```
and since `Alt_fin(X) != 1`, `G` is not MF.

## The upper bound: the parity quotient is residually finite

By the first prerequisite, `G/Alt_fin(X) = C_2 x H` with `H` residually
finite, so the quotient is residually finite.  A countable residually
finite group is MF: enumerate its nonidentity elements, take finite
quotients separating the first `n`, and use their left regular
permutation representations, which are exact; a nonidentity permutation
unitary is at operator-norm distance at least `sqrt(2)` from `I`,
tested on a moved basis vector.  This gives an injective corona
homomorphism, so the quotient map is an MF-target homomorphism with
kernel `Alt_fin(X)` and

```text
Rad_MF(G) <= Alt_fin(X).                                          (2)
```

Together `(1)` and `(2)` give `Rad_MF(G) = Alt_fin(X)`.

## The compression defect equals the same subgroup

**Upper bound.**  In any finite-group image the images of a subgroup `L`
and of a compressed conjugate `vLv^-1` have equal cardinality, so
containment forces equality; hence conjugating an element of `C_J(L)` by
`v` still centralizes the image of `L`, and every compression defect maps
to the identity.  Intersecting the kernels of all finite quotients gives
`D_J(L) = 1` for every residually finite `J`.  The quotient
`G ->> C_2 x H` sends compressors to compressors and centralizers into
centralizers, so `D_G(Gamma) <= Alt_fin(X)`.

**Lower bound.**  For `c in C` put `a_c = u c u^-1`.  Then
`z_c = [a_c, ell]` lies in `D_G(Gamma)` by definition of the defect, `ell`
being in `Gamma` and `a_c` centralizing `u Gamma u^-1`.  For
`d in uCu^-1`, disjointness of `Y` and `Z'` from `(TW2)` gives
`[d, ell a_c^-1 ell^-1] = 1`, hence

```text
[d, z_c] = [d, a_c].
```
`D_G(Gamma)` is normal, so these elements lie in it, and as `c,d` range
over `C` they generate the derived subgroup of `uCu^-1`, a nontrivial
`A_3`.  So `D_G(Gamma)` contains a three-cycle; conjugating by
`Sym_fin(X)` gives every three-cycle, and those generate `Alt_fin(X)`.

Hence `D_G(Gamma) = Alt_fin(X) = Rad_MF(G)`, which is `(DR1)`.

## Simplicity and local finiteness of the radical

`Alt_fin(X)` is the union of the finite alternating groups on the finite
subsets of the infinite set `X`, hence locally finite and infinite, and
it is simple as a direct limit of the simple groups `Alt(F)` along
inclusions with `|F| >= 5`.
