---
rg: 2
id: schur-child-center-has-finite-monomial-sector-proof
kind: route
title: Put all spin simples in monomial bases and irreducibilize by diagonal signs and a cycle
target: schur-child-center-has-finite-monomial-sector
requires:
  - schur-complement-controls-relative-pauli-module
  - finite-predicate-signed-permutation-sector
---

Take the `J=-1` part `V=e_- C[B_f]` of the regular representation, where
`e_-=(1-J)/2`. It is faithful as a group representation: for `g!=1`, the
group-algebra vector `e_-(g-1)` is nonzero (including `g=J`), so left
multiplication by `g` is not the identity. It contains every `J=-1` simple
with positive multiplicity.

Representations of a finite class-two two-group are monomial: after
row and column reduction of its commutator form, every nondegenerate pair acts
by the real Pauli matrices `X,Z`, while radical generators act by signs.
Decompose `V` into simples and choose these tensor-product bases in every
summand. The resulting faithful action `rho(B_f)` consists of signed
permutation matrices.

On selector block `x`, the corrected operator

```text
Q_x=q_(N+1) product_j q_j^(v_j(x))
```

is a product of packet generators, hence a signed permutation in the chosen
basis. Its block direct sum `R_f` on `V` is therefore a signed permutation and
agrees with the group-algebra coefficient `Q_f` on every block.

Let `D_V` be the full finite group of diagonal sign matrices in this basis and
let `z` be one cycle through the whole basis. Define

```text
H_f=<rho(B_f),R_f,D_V,z>
```

inside the finite signed-permutation group of `V`, and take `r_f=R_f`.
The natural representation is irreducible: invariance under `D_V` makes a
subspace a sum of coordinate lines, and invariance under the transitive cycle
forces that sum to be zero or all of `V`. By construction its restriction to
`B_f` and the action of `r_f` have the required forms. Since every selected
summand has `J=-1`, the common sign acts as `-I` on `V`.
