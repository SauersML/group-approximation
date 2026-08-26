---
rg: 2
id: row2-source-factor-sheet-cube-proof
kind: route
title: Collect the paid factor cube and expose its nonzero x53 sheet face
target: row2-source-factor-detects-paid-pauli-sheet
requires:
  - paid-pauli-menu-has-two-row2-indistinguishable-sheets
  - row2-parallel-a2-return-diamond-has-gl8-model
  - binary-leavitt-nonzero-roots-have-uniform-corona-rank-scale
---

Put `S=S_57=x_57(s_1)`.  The already authenticated row-two factorization is

```text
[S,T]=[x_57(s_1),x_78(t_00)]=x_58(s_1t_00)=A_2.       (1)
```

The factor `S` commutes with `Y_2=x_83(b_2)`, but it does not commute with
`H=x_73(h)`.  The adjacent-root Steinberg relation gives

```text
[S,H]=x_53(s_1h).                                     (2)
```

This coefficient is nonzero without using a normal-form theorem.  If
`s_1h=0`, left multiplication by `t_1` would give `h=0`.  But

```text
h s_1=(t_1+s_0t_1)s_1=1+s_0.
```

The equality `1+s_0=0` would imply `s_0=1`; left multiplication by `t_1`
would then give `0=t_1s_0=t_1`, contradicting `t_1s_1=1`.  Thus `s_1h` is
nonzero.  Its elementary image is `I+(s_1h)E_53`, so the root in `(2)` is
nonidentity already in the elementary quotient and therefore in the
Steinberg group.

Now collect the other face directly.  Since

```text
[S,D]=x_58(s_1d),             db_2=h,
```

one more adjacent-root commutator yields

```text
[[S,D],Y_2]=x_53(s_1db_2)=x_53(s_1h)=[S,H].           (3)
```

All roots occurring on the right after collection have common initial
index `5` and commute.  Since `S` commutes with `Y_2` and
`Y_2^(-1)DY_2=DH`, conjugating `[S,D]` gives

```text
Y_2^(-1)[S,D]Y_2=[S,DH]=[S,D][S,H].                  (4)
```

This proves the factor cube and the two distinct sheet signatures.  The
same calculation with `T` instead of `D` gives

```text
[[S,T],Y_2]
 =x_53((s_1t_00)(s_00t_1))
 =x_53(s_1t_1)=x_53(q),                               (5)
```

which is the established middle-index Heisenberg ejection
`[A_2,Y_2]`.  Since the `53` root group is additive in characteristic two,
the exact comparison is

```text
[S,H]=[A_2,Y_2] x_53(s_1s_0t_1).                     (6)
```

Thus `(3)` is not an external root mover: it extends an actual factor-level
row incidence already present in the native inventory.  The second factor
in `(6)` is precisely the residual paid-sheet coefficient; it is not known
to vanish after compression to a paid or signed-source cut.

Finally, the universal nonzero-root comparison applies to the root in
`(2)`.  If `p_K` and `p_z` are the nontrivial spectral projections of its
image and the marked root in a norm corona, then

```text
[p_z] <= 4[p_K].                                       (7)
```

After marked active reblocking this gives the asserted positive rank scale.
Equation `(7)` does not identify the `K` carrier with the signed source; it
only rules out restoring composite-level sheet blindness by killing the new
factor face globally.  No current result says that the paid constant atom
or `Q=e_(L_0,lambda_0)` reduces `S`, so compressing `(3)--(6)` to either cut
would introduce uncontrolled boundary terms.  This route makes no such
compression.
