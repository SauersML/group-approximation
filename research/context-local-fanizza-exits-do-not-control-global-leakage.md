---
rg: 2
id: context-local-fanizza-exits-do-not-control-global-leakage
kind: claim
title: Context-local Fanizza exits do not control the localized non-CE leakage functional
distinct_from:
  localized-non-ce-leakage-forces-cross-gram-overlap: that obtains overlap once the off-capacity leakage is a globally reducing BCS-quiet corner; this proves that the currently established context-local packet bridges do not supply that hypothesis and isolates the exact mixed energy which would.
  context-atom-tag-bridge-installs-child-carrier: that proves the child survivor reduces its complete owning context and explicitly makes no assertion about variables in other contexts; this exhibits an exact finite-dimensional obstruction to upgrading that conclusion without a new mixed two-cell.
  finite-packet-graph-atlases-have-a-regular-stationary-flow: that constructs stationary vertex and edge multiplicities for every finite packet graph; this uses the Bass--Serre normal form to show that a private leakage projection is moved by a shared variable outside its leaf context.
  capacity-gated-common-corner-bcs-two-cell: that gives the positive replacement by forcing every allowed context packet intertwiner to have the same off-capacity source projection.
---

Let `B` be the fixed shared Fanizza BCS, with shared involutions `Z_x` and
finite residual list `R_B`.  Suppose `C,E_1,...,E_m` are projections in a
matrix algebra and

```text
[C,E_i]=0,
L_i=(1-C)E_i.                                           (CFL1)
```

The functional used in
`localized-non-ce-leakage-forces-cross-gram-overlap` is

```text
Lambda
 =sum_i sum_x ||[L_i,Z_x]||_2^2
  +sum_i sum_(R in R_B)||R(Z)L_i||_2^2.                (CFL2)
```

The currently established Fanizza occurrence bridges do **not** bound
`Lambda` by their named relator energy.  They control only variables and
residuals in the owning context.  A new relation involving the exit, the
capacity cut, and the shared tuple before the context split is mandatory.

## Exact mixed-energy reduction

There is nevertheless no additional analytic mystery in `(CFL2)`.  Define

```text
E_mix
 =sum_x ||[C,Z_x]||_2^2
  +sum_i sum_x ||(1-C)[E_i,Z_x]||_2^2
  +sum_i sum_(R in R_B)||(1-C)R(Z)E_i||_2^2.           (CFL3)
```

There is a constant `K_B`, depending only on the fixed finite residual list,
such that every matrix tuple satisfies

```text
Lambda <= K_B E_mix.                                   (CFL4)
```

Indeed,

```text
[L_i,Z_x]
 =(1-C)[E_i,Z_x]-[C,Z_x]E_i,                           (CFL5)
```

and hence

```text
||[L_i,Z_x]||_2^2
 <=2||(1-C)[E_i,Z_x]||_2^2+2||[C,Z_x]||_2^2.          (CFL6)
```

Similarly,

```text
R(Z)L_i
 =(1-C)R(Z)E_i-[R(Z),C]E_i,                            (CFL7)
```

so its squared norm is at most twice the sum of the squared norms of the two
terms on the right.  Every member of `R_B` is one fixed noncommutative
polynomial in the `Z_x`.  Fixed-length commutator telescoping gives

```text
sum_(R in R_B)||[R(Z),C]||_2^2
 <=K'_B sum_x||[Z_x,C]||_2^2.                          (CFL8)
```

Summing `(CFL6)--(CFL8)` proves `(CFL4)`.  Thus `(NCL13)` would follow from
one estimate

```text
E_mix <= K E_rel+o(1).                                 (CFL9)
```

This is strictly more precise than asking vaguely for an approximately
reducing exit.  The relations must force only the **off-capacity blocks** of
the exit commutators and BCS residuals to vanish.  Requiring the whole `E_i`
to be BCS-quiet is too strong: the corner-localized non-CE gap would then kill
the entire exit separately, hiding the root problem in a one-context cell.

## Exact finite countermodel to context-local control

The native additive incidence has the leaf context

```text
C_X={O_Q,X_(m,0),X_tilde},                              (CFL10)
```

attached to the remaining incidence only through the separator `O_Q`.
Consider any finite packet/occurrence atlas obtained from the established
context-local bridges, before adding a genuinely mixed two-cell.  Its local
part is a finite graph of finite groups.  Let `G_X` be the vertex group over
`C_X`, let `H=<O_Q,...>` be its edge group, and let

```text
0!=L in C[G_X]
```

be a private packet leakage projection not contained in `C[H]`.  Such a
projection is exactly what an off-capacity private book/radical atom is; if
all leakage lay in the separator algebra, the context-private packet would
not be carrying the exit.

Choose a shared involution word `Y` from the rest of the Fanizza incidence
which is not in `H`.  In the Bass--Serre left regular representation,

```text
[L,lambda(Y)]!=0.                                      (CFL11)
```

To see this, choose a nonzero coefficient of `L` on some
`g in G_X-H`.  The supports of `gY` and `Yg` are distinct reduced normal
forms, so the corresponding coefficient survives in the commutator.  All
vertex, edge, context-local bridge, and packet relations hold exactly.

The fundamental group of a finite graph of finite groups is virtually free
and residually finite.  Take a chain of finite quotients separating every
word in the finite support of `(CFL11)`.  Their regular representations are
exact finite-dimensional models of all the established local relations and
satisfy

```text
liminf_n ||[L_n,Y_n]||_2^2
 =||[L,lambda(Y)]||_2^2>0,                              (CFL12)
```

while their local named-relator energy is zero.  Consequently no inequality

```text
Lambda <= K E_local+o(1)                               (CFL13)
```

can follow from the context-local packet and occurrence bridges alone.

A two-by-two toy instance displays the same obstruction.  Let

```text
L=diag(1,0),
Y=[[0,1],[1,0]].                                       (CFL14)
```

All involution and local diagonal-context relations can hold exactly, while

```text
||[L,Y]||_2^2=1.                                       (CFL15)
```

The Bass--Serre construction is the actual packet-level version of this
free outside-variable rotation.

## Corrected claim boundary

The existing nodes establish source cuts, fixed packet exactification,
gauge renewal, and context-local survivor reduction.  They do not establish
`(NCL13)`.  In particular, `context-atom-tag-bridge-installs-child-carrier`
correctly states that its survivor reduces `Z'` only in its own context and
makes no assertion about the other BCS contexts.

A convenient explicit sufficient target is `(CFL9)`.  A valid actuator must
contain a mixed capacity-gated two-cell whose decoded matrix consequences
control either the following separate blocks or their cancellation-friendly
common-corner equivalent:

```text
(1-C)[E_i,Z_x]                 for every shared x,
(1-C)R(Z)E_i                  for every R in R_B.       (CFL16)
```

It is not enough to make `C` and `E_i` separately packet-central, and it is
not enough to transport each owning context exactly.  The capacity factor
`1-C` is essential: it allows the canonical/non-CE exact model to carry its
BCS defect inside `C`, while forcing only the excess exit range to be a
matrix BCS corner.  Constructing `(CFL16)` in ordinary group-word
coordinates is exactly the remaining source-specific Connes-embedding
separator; no established finite packet relation currently supplies it.

`capacity-gated-common-corner-bcs-two-cell` gives the weaker
cancellation-friendly form which does not separately require `C` or `E_i`
to reduce the shared tuple.  It is enough to decode, for every context, an
allowed packet intertwiner whose common source Gram projection is exactly
`L_i`.
