---
rg: 2
id: controlled-reflection-cell-has-free-orientation
kind: claim
title: A Pauli controlled-reflection cell has a free multiplicity orientation in the marked spin sector
distinct_from:
  pauli-zero-atom-removes-acceptance-source-deficit: that uses uniqueness of the marked Pauli spin type to make a commuting source occupy every control atom uniformly; this shows that the same uniqueness does not determine a controlled base reflection.
  block-encoded-acceptance-still-needs-corner-return: that assumes the intended controlled reflections are available and isolates the analytic corner return; this proves the exact intended extension and the extra finite representation type which obstructs universal soundness.
  finite-selector-gadget-induction-barrier: that says every finite abelian selector character appears in some ambient representation; this exhibits the precise orientation character already inside the minimal controlled-reflection cell.
---

Fix a control qubit `j` in an extraspecial Pauli group, with Pauli
involutions `X_j,Z_j` and central sign `J_ctl`.  Let `r` be the involution
which should be coherently controlled; in the game application it is one
predicate or consistency reflection.  Make `r` commute with the control
Paulis.  Adjoin an involution `c` with relations

```text
[c,Z_k]=1                     for every k,
[c,X_k]=1                     for k!=j,
[c,r]=1,
c X_j c X_j=r.                                        (COR1)
```

This is the minimal two-coordinate wreath/control cell.  The intended
representation is

```text
c=|0><0|_j tensor I+|1><1|_j tensor r.                (COR2)
```

It exists exactly, but it is not forced by the marked Pauli type.

## Complete marked-spin normal form

On the `J_ctl=-1` sector, the control Pauli group acts as

```text
C^(2^m) tensor M.                                      (COR3)
```

The commutation relations in `(COR1)` imply

```text
c
 =|0><0|_j tensor u_0
  +|1><1|_j tensor u_1,                                (COR4)
```

with the identity on the other control-qubit factors, where `u_0,u_1` are
commuting multiplicity involutions which commute with `r`.  The last
relation in `(COR1)` is exactly

```text
u_0u_1=r.                                              (COR5)
```

Therefore every marked-spin solution is

```text
c
 =|0><0|_j tensor u
  +|1><1|_j tensor ur,                                 (COR6)
```

for an arbitrary multiplicity involution `u` commuting with `r`.  The
intended controlled reflection `(COR2)` is only the special choice `u=I`.

If `H_j` is a Hadamard/Clifford normalizer, then

```text
P_(0,j) H_j c H_j P_(0,j)
 =P_(0,j) tensor u(I+r)/2.                             (COR7)
```

Thus the free orientation sits immediately in front of the desired
acceptance projection.  For several tests the uncontrolled `u_j` occur
between successive acceptance projections, so the finite-game contraction
for the unmodified product does not apply.

## Exact character-twist obstruction

The freedom is visible without representation theory.  The cell admits the
one-dimensional character twist

```text
c -> -c,
all Pauli generators and r fixed.                     (COR8)
```

Every relation in `(COR1)` contains `c` an even number of times.  Tensoring
any exact marked-spin representation by `(COR8)` keeps `J_ctl=-1` and the
same system reflection `r`, but sends `u` to `-u`.  Consequently no condition
which selects only the central Pauli sign can distinguish `(COR2)` from its
opposite orientation.

The full finite wreath version has the same obstruction in larger form.
Its lamp characters of different Hamming weights restrict to the same
marked Pauli spin representation, while a coordinate lamp acts on a
different number of computational atoms.  A central diagonal product fixes
only the parity/ratio of the two blocks, not the first block itself.

Hence:

```text
J_ctl=-1 spin selection
+ exact wreath/Clifford relations
does not force a controlled reflection.               (COR9)
```

An additional orientation tag or higher-dimensional Hecke idempotent can
select `u=I` in the intended finite type, but then its source saturation has
to be authenticated.  This is the finite selector/induction problem which
the unique Pauli spin type was meant to avoid.

## Exact perfect-witness extension

The failure is on soundness, not completeness.  Given any exact unitary
representation of the game reflections `r_1,...,r_m` on `H`, put the Pauli
controls on `C^(2^m)` and define

```text
c_j
 =|0><0|_j tensor I_H
  +|1><1|_j tensor r_j.                                (COR10)
```

The operators `(COR10)` satisfy all cells `(COR1)`, even when the different
`r_j` do not commute, because distinct controller cells need not be
amalgamated through their lamp groups.  With

```text
B_j=H_j c_j H_j,
W_game=B_m...B_1,                                     (COR11)
```

the fresh-control computation is exact:

```text
P_0 W_game P_0=P_0 tensor T_game.                      (COR12)
```

For a perfect commuting/tracial strategy, `T_game(1)=1`, so
`|0^m> tensor 1` is fixed by `W_game`.  The original native mark remains on
the factor `H`.  Thus every desired exact perfect witness extends, with the
choice `u_j=I`.

## Canonical control mass

For the extraspecial group `E_m`, the unique `J_ctl=-1` irreducible has
dimension `2^m` and the group has order `2^(1+2m)`.  Its Plancherel mass in
the regular representation is therefore

```text
(2^m)^2/2^(1+2m)=1/2.                                 (COR13)
```

Conditioned on that spin sector, every computational atom has mass `2^-m`.
Thus the absolute canonical mass of `P_0` in the marked spin block is

```text
tau(P_0 E_-)=2^(-(m+1)).                               (COR14)
```

The source-mass calculation in
`pauli-zero-atom-removes-acceptance-source-deficit` is therefore correct for
a base source commuting with the full control Pauli group.  What fails is
the separate claim that `W_game` has the intended acceptance corner in
**every** marked-spin representation.

## Minimal remaining algebraic datum

The missing finite datum is exactly the orientation equation

```text
P_(0,j)c_jP_(0,j)=P_(0,j),                            (COR15)
```

or its scalar full-overlap form

```text
Re tau(P_(0,j)c_j)=tau(P_(0,j)).                       (COR16)
```

Neither is an ordinary global group relation.  They are Hecke-corner
selection statements.  Once `(COR15)` holds for every test, `(COR12)` and
the Pauli zero-atom source theorem give the one-return target `(PAZ12)`.

Accordingly the requested exact finite packet has the following sharp
status:

- intended controlled-reflection representation: **constructed**;
- canonical marked spin and zero-atom mass: **verified**;
- exact perfect-witness extension: **constructed**;
- universal realization on the sector selected only by `J_ctl=-1`:
  **impossible**, because of `(COR6)--(COR9)`;
- minimal repair: one orientation Hecke moment per controller, or a new
  finite type whose common source must itself be authenticated.
