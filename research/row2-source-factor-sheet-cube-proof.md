---
rg: 2
id: row2-source-factor-sheet-cube-proof
kind: route
title: Collect the paid factor cube and expose its nonzero x53 sheet face
target: row2-source-factor-detects-paid-pauli-sheet
requires:
  - paid-pauli-menu-has-two-row2-indistinguishable-sheets
  - row2-parallel-a2-return-diamond-has-gl8-model
  - center-chain-mixed-hecke-overlap-is-common-pauli-source
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

For completeness, the co-minimal detector in the signed-source normalizer
table is the common tail `A_1=x_47(a_1)`, `a_1=s_1t_0`.  The common-source
calculation proves that `A_1` normalizes `Q=e_(L_0,lambda_0)`, and direct
collection gives

```text
[A_1,H]=x_43(a_1h).                                   (8)
```

The coefficient is nonzero.  Indeed `a_1h=0` would imply `t_0h=0` after
left multiplication by `t_1`; right multiplication by `s_1` would then
give `t_0+1=0`.  But `t_0=1` and `t_0s_1=0` force `s_1=0`, contradicting
`t_1s_1=1`.  Thus `(8)` is another nonidentity elementary root and is tied
to both Hecke maps `u_1=B_2A_1`, `u_2=B_3A_2A_1`.

This extra source-normalizer incidence still does not license compression:
`A_1Q=QA_1` is known, but no current result says that `H` normalizes `Q` or
that `Qx_43(a_1h)Q` has positive mass.  Accordingly neither `(8)` nor the
coefficient-shorter row-two detector `(2)` is claimed to select a signed
source sheet.

Here is the exact compression formula.  Put `U=A_1`, `K_U=[U,H]`,
`R=QHQ`, and `L=QH(1-Q)`.  Root operators are involutions in characteristic
two, and `U` commutes with `Q`.  Inserting `Q+(1-Q)` between the first `H`
and the second `U` gives

```text
QK_UQ
 =QUHUHQ
 =U(QHQ)U(QHQ)+U(QH(1-Q))U((1-Q)HQ)
 =URUR+ULUL^*.                                        (9)
```

Consequently

```text
Q(K_U-1)Q=URUR-Q+ULUL^*.                              (10)
```

Neither term forces a lower bound.  This is not merely a missing estimate.
On the ordered basis of `C^4`, set

```text
Q=diag(1,0,0,0),          U=diag(1,1,-1,-1),
H=SWAP_(2,3),             K_U=diag(1,-1,-1,1),
z=diag(-1,-1,1,1),        V=SWAP_(1,3).               (11)
```

Then `K_U=[U,H]`, `UQ=QU`, `HQ=QH=Q`, and hence `L=0`, `R=Q` and
`Q(K_U-1)Q=0`.  Nevertheless `K_U` is nonidentity, its negative spectral
projection has rank two, `zQ=-Q`, and `z=VK_UV^(-1)`, so even the strongest
global rank comparison is exact in this model.

To include the signed-source datum literally, represent `L_0` diagonally
by its character `lambda_0` on `QH` and by three copies of the trivial
character on `(1-Q)H`.  Since `lambda_0` is nontrivial, its signed Reynolds
average is exactly `Q`.  Both `U` and `H` preserve the two character
isotypic pieces, so the source-normalizer assertions hold.  This is a
four-dimensional exact model of precisely the compression, signed-character,
and global detector-rank data used above.  It is not a representation of
the full Steinberg group, and it proves the sharp scoped fence: those data
alone allow a globally nontrivial sheet detector to act trivially on the
entire marked signed source.
