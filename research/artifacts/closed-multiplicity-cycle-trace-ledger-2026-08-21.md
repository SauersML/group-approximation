# Closed multiplicity-cycle trace ledger

**Date:** 2026-08-21  
**Status:** proved scalar endpoint; common-reservoir extraction remains open

Suppose a decoded finite matrix model has carrier projections
`P_0,...,P_m`.  At edge `e`, `r_e` approximate left/right block-map pairs
try to identify `r_e` copies of `P_e` with `P_(e+1)`.  Normalized cyclic
trace gives

```text
|tr(P_(e+1))-r_e tr(P_e)|
 <= ||sum_j S_(e,j)T_(e,j)-P_(e+1)||_2
    + sum_j ||T_(e,j)S_(e,j)-P_e||_2.
```

Unfolding around a cycle whose final projection returns to `P_0` yields

```text
(prod_e r_e - 1) tr(P_0)
 <= return_error
    + sum_e (prod_(k>e) r_k) edge_error_e.
```

For `m` binary cells, with all three defects at each cell bounded by
`epsilon`, this simplifies exactly to

```text
tr(P_0) <= 3 epsilon + return_error/(2^m-1).
```

The important point is the quantifier: the error constant does not grow with
the number of binary levels.  The expanding weights that appear when the
recurrence is unfolded cancel against the total expansion `2^m-1`.

This proves the desired contractive accounting once a group-word decoder has
forced every step to use one closed physical multiplicity reservoir.  It does
not exclude rectangular escape: if a child enlarges the recovered label
space and shrinks multiplicity, the source and target projections in the
ledger have not been identified on a closed cycle.  Consequently the live
theorem is precisely same-reservoir extraction, not a further accumulation or
rounding estimate.

The lemma applies verbatim to:

- the affine--Leavitt boundary lane after `same-orbit-closure`;
- the Schur--Clifford multiplicity-return lane after fixed packet-scale
  contextual holonomy;
- any trace-cyclic return cell whose decoded source and target carriers close
  after finitely many steps.
