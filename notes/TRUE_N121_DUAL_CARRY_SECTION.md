# An exact dual integral-carry section for all seven level-121 directions

Date: 2026-08-12

## 1. Outcome

The determinant-one primal packet at level `121` now has a complete explicit
dual integral section

```text
s_121:Q_121^# -> M_Sigma,
P_Sigma s_121=id.                                             (NDS1)
```

It covers all seven new rational harmonic directions simultaneously.  After
exact sparse solution and converged greedy reduction by literal range rows,
the seven ambient integral lifts have Gram matrix

```text
[[480, -5,-23,-11, 97,-1, -1],
 [ -5,188,-20,-25, 17,-2, -1],
 [-23,-20, 67, 14,-35, 2,  2],
 [-11,-25, 14, 91,-34, 0,-17],
 [ 97, 17,-35,-34,226,-1, -1],
 [ -1, -2,  2,  0, -1, 6,  0],
 [ -1, -1,  2,-17, -1, 0, 34]].                              (NDS2)
```

The corresponding exact generalized characteristic polynomial is stored in
the certificate.  Its largest root is

```text
483.52844638109316543710379562588599417330862380...,
```

so

```text
||s_121||
 <=21.989280260642756322682174499137928640525387696....       (NDS3)
```

The displayed section has maximum coefficient `2`, support sizes

```text
468,188,67,91,220,6,34,                                      (NDS4)
```

and squared norms

```text
480,188,67,91,226,6,34.                                      (NDS5)
```

This is a certified upper bound, not the least section norm and not a CVP
optimum.  It is nevertheless the first exact numerator-side certificate for
the entire rank-seven square-level harmonic lattice.  Together with the
previous dual-systole certificate, it proves that every level-`121` harmonic
carry class has uniformly finite lift ratio within this chart.

The important algorithmic gain is larger than the numerical improvement.
The exact integral solve itself takes about `0.057` seconds.  The previous
generic primitive-kernel/HNF attempts exceeded `10` and `15` minute caps.
Thus the determinant-one packet changes the appropriate computation from a
huge lattice normal form to seven right-hand sides of one sparse local
integer system.

## 2. Direct packet equations

Let `c_1,...,c_7` be the certified packet cycles.  By
`TRUE_PACKET_TO_DUAL_CARRY_SECTION.md`, their projections form a `Z`-basis
of `Q_121` and

```text
K=S_sat directSum <c_1,...,c_7>_Z.                            (NDS6)
```

Choose `625` actual rows `b_1,...,b_625` of `d_3` which span the rational
boundary space.  An ambient integer vector `z_i` lifts the packet-dual vector
`u_i in Q_121^#` exactly when

```text
<z_i,b_j>=0,              1<=j<=625,
<z_i,c_j>=delta_ij,       1<=j<=7.                            (NDS7)
```

Thus all seven lifts are columns of an integral solution to a sparse system
with dimensions

```text
632 equations x 1940 variables,    6746 nonzero coefficients. (NDS8)
```

Solving `(NDS7)` is enough: annihilation of the selected `b_j` implies
annihilation of every row of `d_3`, because the selected rows span the same
rational space.  Exact post-verification checks both

```text
d_3 Z^T=0,             C Z^T=I_7.                            (NDS9)
```

The first identity puts every lift in `M_Sigma`; the second identifies its
cycle projection with the packet-dual basis.  These are the defining
identities of `(NDS1)`.

## 3. Content-normalized unit elimination

The sparse solver uses only integral row operations and unit pivots.  It
maintains the seven right sides simultaneously.

1. Choose a coefficient `+1` or `-1` as pivot.
2. Clear its variable from every other equation by an integral row
   operation.
3. If a residual row has coefficient content `d>1` and all seven targets are
   divisible by `d`, divide the entire equation by `d`.  This preserves its
   exact integral solution set.
4. Continue until no equation remains, then back-substitute with all free
   variables set to zero.

For `(NDS8)`, the exact profile is

```text
round 0: 630 unit pivots, 2 residual rows,
         residual contents 2 and 4;
round 1: divide those contents, then 2 unit pivots, no residual. (NDS10)
```

There are only `938` elimination updates and the peak active number of
nonzeros never exceeds the initial `6746`.  Hence there is no fill-in
explosion.

The contents `2` and `4` in `(NDS10)` are properties of this selected
presentation and pivot order.  They are useful evidence that all non-unit
arithmetic is localized to two equations, but they are **not** by themselves
Smith invariants or a theorem that the intrinsic obstruction is purely
two-primary.  The invariant conclusion is the completed integral section
verified by `(NDS9)`.

## 4. Range reduction

The raw unit-pivot section is exact but poorly conditioned.  Its largest
generalized singular value gives norm about `149.93`.  Every row of
`d_2^T` lies in the range lattice `L`, so subtracting an integral multiple of
such a row from an individual lift preserves `(NDS9)`.

The reducer cycles through all nonzero rows `g` of `d_2^T` and, for a current
lift `z`, subtracts the nearest integer multiple of `g` whenever this strictly
decreases `||z||^2`.  The numbers of accepted moves are

```text
1501,986,416,200,93,67,41,21,9,5,0.                         (NDS11)
```

Thus this particular coordinate descent has converged.  It changes the lift
Gram from one with diagonal

```text
24958,1222,145,548,3350,33,95
```

to `(NDS2)`, and decreases the section norm from about `149.93` to `(NDS3)`.
The terminal condition only says that no single displayed range generator
improves any lift; combinations of generators, LLL/Babai, or exact CVP may
still lower the section norm substantially.

## 5. Meaning for TRUE

Level `121` was the first chart with seven entirely new rational harmonic
directions.  Three distinct issues are now exact there:

1. the primal packet has determinant one and bounded synthesis;
2. the dual systole is `0.4532023076...`, above the spherical danger
   threshold; and
3. every dual class has an explicit integral ambient lift through `(NDS1)`.

Consequently no denominator collapse or failure of integral lift exists at
this chart.  The value `(NDS3)` is larger than the rank-two section bounds
`7.4902` at level `53` and `11.7937` at level `61`, but it is only an upper
bound obtained from a local reducer.  It neither proves growth nor threatens
the already certified absence of sub-threshold classes at level `121`.

The family theorem remains:

> construct determinant-one primal packets and packet-dual integral lifts
> whose synthesis/Gram bounds are uniform over every projective chart.

The present computation gives a practical route to test and discover that
structure: solve the direct packet equations, inspect the tiny post-unit
residual, and reduce only seven lift rows.  It is no longer necessary to
construct the full primitive cycle lattice at each level.

## 6. Certificate and implementation

```text
experiments/projective-cellular-n121-dual-sparse-20.json
SHA-256 e94d8c9f68d2128085b015119a68ad9d13e27e1e6467630686fa88f3e98d6ff7

experiments/sl3_projective_dual_section_sparse.py
```

The certificate contains all raw and reduced lifts sparsely, both exact Gram
matrices, the exact `Q^#` Gram matrix, the generalized polynomial and all
seven approximate roots, the determinant-one packet pairing, the complete
elimination diagnostics, and the source hashes.  The script rebuilds the
cellular matrices, verifies every identity in `(NDS9)`, and refuses to claim
a section if any non-unit residual survives.
