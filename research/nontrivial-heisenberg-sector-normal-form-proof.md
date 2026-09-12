---
rg: 2
id: nontrivial-heisenberg-sector-normal-form-proof
kind: route
title: Apply finite Stone-von Neumann and Schur on the multiplicity factor
target: heisenberg-sector-is-schrodinger-times-free-multiplicity
requires: []
---

The finite Stone--von Neumann theorem for the nondegenerate group `(HSF1)`
says that for every nontrivial character `zeta` of `<Z>` there is exactly one
irreducible representation with central character `zeta`, and its dimension
is `p^N`.  Complete reducibility on the central spectral summand `(HSF2)`
therefore gives `(HSF3)`.  Taking dimensions gives the first part of
`(HSF4)`, and the commutant form in `(HSF4)` is Schur's lemma with
multiplicity.

In the standard Schrödinger model, `X(F_p^N)` is diagonal with each of its
`p^N` characters occurring once.  Tensoring with `C^(m_zeta)` makes every
character multiplicity exactly `m_zeta`, proving the polarized trace
statement.

Because `alpha` fixes `Z`, the representation
`pi_(N,zeta) after alpha` has the same nontrivial central character.  Finite
Stone--von Neumann supplies a unitary `U_alpha` intertwining it with
`pi_(N,zeta)`.  If `W` is any other implementer, then

```text
(U_alpha^* tensor I)W
```

commutes with `pi_(N,zeta)(H_N) tensor I`.  The commutant computation in
`(HSF4)` makes it `I tensor V` for a unique unitary `V`, proving `(HSF6)`;
the converse follows by direct substitution.

Finally write

```text
F_p^M=F_p^N directSum F_p^(M-N),
l2(F_p^M)=l2(F_p^N) tensor l2(F_p^(M-N)).
```

The first-coordinate `H_N` acts as `pi_(N,zeta) tensor I`, which is `(HSF7)`
and exposes the full `U(p^(M-N))` commutant gauge.  A nonidentity cyclic shift
on a space of dimension `p^(M-N)>=2` has normalized trace zero, so

```text
||V-I||_2^2=2-2 Re tr(V)=2.
```

It commutes with the restricted Heisenberg action, and therefore changes no
central projection, character multiplicity, restriction density, or finite
group word.  Adding a finite tensor tag and using `V tensor I` proves the
last assertion.
