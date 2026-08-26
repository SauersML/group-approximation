---
rg: 2
id: aggregate-morita-common-opposite-return-gl3-square-proof
kind: route
title: Factor the common reverse Morita return into two finite three-coordinate packets
target: aggregate-morita-common-opposite-return-has-gl3-square-model
requires:
  - aggregate-morita-row-column-fold-has-d8-square-model
  - outer-root-leavitt-table
  - atomic-leavitt-gap-on-nonzero-matrix-corner
---

For `k_0=9,k_1=10`, the ordinary non-opposite Steinberg relation gives

```text
[x_87(1),x_(7,k_i)(s_i)]=x_(8,k_i)(s_i),
[x_(k_i,8)(t_i),x_87(1)]=x_(k_i,7)(t_i).
```

Their matching commutator is

```text
[x_(8,k_i)(s_i),x_(k_i,7)(t_i)]
  =x_87(s_it_i)=R_i.
```

The different intermediate coordinates and `t_is_j=0` for `i!=j` give
all crossed-child commutations.  Root addition and
`q_0+q_1=s_0t_0+s_1t_1=1` give `R_0R_1=D`.  The aggregate roots have unit
coefficient, so the ordinary rank-one Whitehead relation gives
`NDN=DND` directly.  No opposite-root identity at the proper child
idempotents is needed.

For the finite model, in one copy of `GL_3(F_2)` let `e_ab=I+E_ab`.  Direct
multiplication gives

```text
[e_12,e_23]=e_13,
[e_31,e_12]=e_32,
[e_23,e_31]=e_21,
[e_32,e_21]=e_31,
e_13e_31e_13=e_31e_13e_31.
```

Use these six matrices in the two separate factors as in `(ACR7)`.  The
other factor commutes, so every crossed row is automatic, while diagonal
pairing gives both aggregate parents in `(ACR8)`.  The executable audit
`experiments/aggregate_morita_returned_opposite_fold_audit.py` verifies the
entire displayed table over `F_2`, including the parent braid and
nontriviality of `C_1`.  It also exhausts the old eight-element dihedral
factor and proves that `(ACR6)` has only the identity solution, so the
previous `D_8 times D_8` model cannot extend across the new row.

The left regular representation of this finite group is an exact unitary
model.  Since `C_1` is nonidentity, its regular action has nonzero negative
spectral mass.  The Atomic Leavitt Gap therefore fences any claimed
vanishing-modulus Atomic Morita Return from this bounded occurrence menu.
