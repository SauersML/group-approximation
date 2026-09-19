---
rg: 2
id: translation-symmetrized-schur-child-reset-proof
kind: route
title: Translate selector signs while permuting shifted commutator pencils
target: translation-symmetrized-schur-child-reset
requires:
  - schur-child-center-sign-flip-is-group-automorphism
  - finite-schur-clifford-packet-flexible-hs-exactification
  - shared-overlap-controls-packet-multiplicity-vector
---

For copy `a`, impose

```text
[p_i^(a),q_j^(a)]
 =J^(c_ij+sum_l a_(ij,l)a_l) product_l z_l^(a_(ij,l)),
[p_i^(a),q_*^(a)]=J^((e_t)_i),
```

with the usual involution and same-side commutation relations. Make
noncentral generators from distinct copies commute. This is consistent: it
is the central extension of the direct sum of the copy quotient spaces by
`<J,z_1,...,z_k>`, with the displayed block-diagonal alternating
commutator form. In particular every copy, including `C_f^(0)`, embeds.

Apply `(TSR1)` to the first displayed commutator. Its right side becomes

```text
J^(c_ij+A_ij dot a) product_l (J^(b_l)z_l)^(a_(ij,l))
 =J^(c_ij+A_ij dot (a+b)) product_l z_l^(a_(ij,l)),
```

which is exactly the relation in copy `a+b`. The last child column is
constant, so its relations are also preserved. Cross-copy commutation and
all involution relations are preserved. The maps compose by addition in
`X`, proving the translation action. The proof of
`schur-child-center-sign-flip-is-group-automorphism` applies independently
to each copy and gives `(TSR2)`; conjugating `eta_a` by `tau_b` gives
`eta_(a+b)`. This constructs the finite semidirect product.

Now let `rho` be an exact `J=-1` representation. The joint selector spaces
`H_x` are genuine central spectral subspaces. The unitary implementing
`tau_b` carries `H_x` onto `H_(x+b)`, so all have dimension
`dim(H)/2^k`. On `H_x`, the sector algebra of `C_f^(0)` is

```text
M_D(C) tensor C[C_2],
```

because `U_f(x)` has rank `N` and the child has one radical generator.
Its two simples therefore both have dimension `D`. The unitary implementing
`eta_0` sends the corrected center `Q_f` to `-Q_f` and preserves `H_x`, so it
interchanges their isotypic subspaces. Each has half the dimension of `H_x`,
which proves `(TSR4)`.

The quantitative statement is the standard fixed-finite-table argument.
Word telescoping gives an all-pairs defect for `R_f`; flexible finite-group
exactification gives an exact representation with dimension-independent
loss; and `(OMV1)` transfers its exactly balanced `C_f^(0)` type vector to
any separately corrected copy on the common overlap. Finally, the normal-form
theorem for a free product with amalgamation embeds both factors, so attaching
the reset cannot kill a marked word in the base.
