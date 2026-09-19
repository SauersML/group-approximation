# The braid prefix atlas has no positive label-averaging projection

The rank-one interface is

```text
xyx=yxy.
```

Take the two directed prefix paths from the identity to the common endpoint.
Number their union cyclically by

```text
p_0=e, p_1=x, p_2=xy, p_3=xyx=yxy, p_4=yx, p_5=y.
```

The oriented edges carrying `x` are

```text
X={(0,1),(2,3),(5,4)},
```

and those carrying `y` are

```text
Y={(1,2),(0,5),(4,3)}.
```

Let `L_br subset M_6` be the self-adjoint linear space whose entries are
constant on `X`, constant on `Y`, constant on the reversed classes by
adjoint, and otherwise unrestricted.  The affine unital correlation slice
adds diagonal entries equal to one; the linear obstruction already occurs in
`L_br`.

## 1. No fixed-point or ucp-expectation repair

The space `L_br` contains every diagonal matrix unit `E_ii`.  Suppose a ucp
idempotent `Phi:M_6 -> M_6` had range `L_br`.  Then

```text
Phi(E_ii)=E_ii
```

for every `i`.  A projection fixed by a ucp map satisfies equality in both
Schwarz inequalities, so every `E_ii` belongs to the multiplicative domain.
Consequently

```text
Phi(E_ii T E_jj)=E_ii Phi(T) E_jj,
```

and `Phi(E_ij)=lambda_ij E_ij`: `Phi` is a Schur multiplier over the diagonal
masa.

But

```text
A_X=E_01+E_23+E_54
```

belongs to `L_br`, so `Phi(A_X)=A_X`.  Entrywise action forces
`lambda_01=lambda_23=lambda_54=1`, whence each of
`E_01,E_23,E_54` lies in the range.  None lies in `L_br`, because its other
two `X` entries are zero.  Contradiction.

If `L_br` were the fixed-point space of a finite permutation or unitary
conjugation action, group averaging would be just such a ucp projection.
Thus no action of that kind exists.  Equivalently, because all diagonal
units are fixed, every acting unitary would have to commute with the diagonal
masa, and diagonal conjugations can impose zero patterns but cannot average
three different matrix positions into one coefficient.

## 2. The orthogonal averaging map is explicitly nonpositive

Let `T` preserve all entries except that it replaces the three entries on
`X` by their arithmetic mean, does the same on `Y`, and applies adjoints on
the reversed edges.  This is the Hilbert--Schmidt orthogonal projection onto
`L_br`.

Set

```text
v=(-1,0,1,-1,0,1)^t,       q=(-1,-1,-1,1,1,1)^t.
```

A direct rational calculation gives

```text
q^* T(vv^*) q = -16/3.                                  (B1)
```

There is an even quicker diagnosis: positions `1` and `4` have zero diagonal
in `T(vv^*)`, while label averaging creates nonzero entries in those rows.
A positive matrix with a zero diagonal entry has the corresponding row and
column zero, so `T(vv^*)` cannot be positive.

There is a smaller negative witness inside the braid cell.  Retain only the
four prefixes

```text
e, x, xy, xyx
```

and average the two entries labelled `x`, at `(0,1)` and `(2,3)`.  For
`v=(1,1,0,0)^t`, the positive matrix `vv^*` is sent to a matrix whose
principal lower `2 by 2` block is

```text
[[0,1/2],[1/2,0]],
```

with eigenvalue `-1/2`.  Hence positivity failure is caused by repeated-edge
averaging itself and appears even on a chordal path.  The six-vertex support
is relevant for a different reason: it is the first nonchordal graph carrying
the complete braid equality.

## 3. Minimality and consequence

The support graph is the alternating six-cycle formed by the two length-three
braid paths.  Deleting any vertex turns it into a forest, hence a chordal
partial-matrix pattern covered by the standard chordal lifting theorem.  The
full braid cell is therefore the support-minimal **nonchordal** pattern for
this derivation, although the natural repeated-label projection is already
nonpositive on the four-prefix path above.

This does not refute existence of a nearby positive, exactly labelled matrix
for the special Chevalley microstates.  It proves that such a matrix cannot
be obtained by a fixed permutation/unitary average or by any ucp conditional
expectation onto the natural repeated-label space.  Joining the quarter-turn
cell could only help by imposing additional coupled structure; it cannot turn
the natural label-class projection itself positive.  The mixed
positive/affine intersection must still be solved rather than averaged away.
