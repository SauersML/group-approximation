---
rg: 2
id: shared-cousin-matrix-fusion-proof
kind: route
title: Quotient the top scalar root in a finite three-object matrix-unit chart
target: shared-cousin-arm-loop-has-finite-matrix-fusion
requires:
  - outer-root-leavitt-table
  - leavitt-range-sum-fold-is-first-object-erasing-row
---

Let

```text
R=M_3(F_2)
```

on the ordered basis `(p,q_u,q_v)`, writing the same symbols for the three
diagonal matrix units.  Define `(SCF3)`.  Direct matrix-unit multiplication
gives

```text
t_i s_j=delta_(ij)p,
s_i t_i=q_i,
t_u s_u t_v s_v=p,                                    (1)
```

and every mismatched version of the last product is zero at its first
mismatch.  These are the required literally shared coefficient identities.
The coefficient-basis transposition exchanging `p` and `q_i` swaps `t_i`
with `s_i`, sends `p` to `q_i`, and conjugates every other named matrix-unit
occurrence accordingly.  It is the finite partial-Whitehead action.

Let

```text
N=UT_5(R),                    z(r)=I+E_15(r).           (2)
```

The subgroup `z(R)` is central in `N`, since the top-right root position has
no composable strictly upper-triangular neighbor.  Put

```text
G_0=N/<z(1)>.                                          (3)
```

The root map on the center is additive, so in `G_0`

```text
z(q_u)z(q_v)=z(q_u+q_v)
             =z(1+p)=z(p),                            (4)
```

proving the fold.  The class of `z(p)` is nonidentity: the kernel imposed in
the central additive group is exactly the one-dimensional scalar subspace
`F_2 1`, and the rank-one projection `p` is not scalar.

Permutation matrices on the coefficient basis act on `R` by conjugation,
hence entrywise on `N`.  They fix the coefficient identity and preserve the
central subgroup `<z(1)>`, so the two source/range transpositions descend to
automorphisms of `G_0`.  Form the finite semidirect product by the generated
`S_3` actor.  Equations `(1)` groupify through ordinary adjacent-root
commutators in `N`, and the actor gives every Whitehead occurrence square
using those same elements.

The left regular representation of this finite semidirect product satisfies
all tested words exactly.  Since `z(p)` remains nonidentity, its nontrivial
spectral projection is nonzero.  Therefore the tested shared-arm mixed loop
and central fold cannot imply `(BAC1)`.
