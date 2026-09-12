---
rg: 2
id: finite-type-additive-overlap-obeys-row-column-capacity
kind: claim
title: Additive finite-type equality must fill every restriction-overlap row and column
artifacts:
  - research/finite-type-additive-overlap-capacity-proof.md
distinct_from:
  finite-type-restriction-overlap-defect-formula: that computes every cross overlap and the total defect exactly; this extracts local row and column capacity obstructions that remain valid before the whole overlap table is known.
  regular-subgroup-branching-is-hall-balanced: that proves regular Plancherel restriction weights always satisfy Hall; this treats arbitrary selected finite types and detects strict deficits caused by small transported subgroup intersections.
  canonical-trace-forbids-supercritical-character-packing: that upper-bounds how many orthogonal conjugates can be packed into the unit; this lower-bounds how much restriction capacity is required to cover each source atom by an additive target sum.
---

Let `(p_i)_(i in I)` and `(r_j)_(j in J)` be finite orthogonal families
of transported central finite-type projections in `C[Gamma]`. Write

```text
p_i=g_i z_(H_i,rho_i) g_i^(-1),
r_j=h_j z_(K_j,sigma_j) h_j^(-1),
A_i=g_iH_ig_i^(-1),        B_j=h_jK_jh_j^(-1),
L_ij=A_i intersect B_j,
d_i=dim(rho_i),             e_j=dim(sigma_j),
P=sum_i p_i,                R=sum_j r_j.                 (ARC1)
```

Define the row and column capacities

```text
C_i=sum_j e_j^2/[B_j:L_ij],
D_j=sum_i d_i^2/[A_i:L_ij].                              (ARC2)
```

Then the rows and columns give quantitative lower bounds for the additive
defect:

```text
||P-R||_2^2 >= sum_i tau(p_i) max(0,1-C_i),
||P-R||_2^2 >= sum_j tau(r_j) max(0,1-D_j).              (ARC3)
```

Consequently an exact additive identity `P=R` requires

```text
C_i>=1 for every i,             D_j>=1 for every j.      (ARC4)
```

This is a genuine many-to-many obstruction. If all target atoms are
character idempotents, then `e_j=1`; a source atom can be covered only if

```text
sum_j 1/[B_j:L_ij]>=1.                                  (ARC5)
```

In particular, `n` target character atoms whose intersections with one
source all have index greater than `n` cannot add up to a projection
containing that source, regardless of coefficient phases or cycle
presentation.

The boundary case is rigid. If `P=R` and `C_i=1`, then every cross term
saturates its full intertwiner-space bound. Whenever `p_i r_j!=0`, both
restricted types on `L_ij` are scalar copies of the same one-dimensional
character. Thus a capacity-one row is restriction-theoretically scalar on
every cross intersection; genuinely non-scalar restriction interference
requires strict capacity surplus.

For the transverse `D_8` cell of
`finite-type-restriction-overlap-defect-formula`, every target is
one-dimensional and each intersection has index two. Hence each row has
capacity `1/2+1/2=1`. The example exactly saturates `(ARC4)`, explaining
both its additive `2 by 2` equality and its finite-packet rigidity.
