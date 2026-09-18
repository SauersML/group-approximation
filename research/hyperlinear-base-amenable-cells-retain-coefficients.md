---
rg: 2
id: hyperlinear-base-amenable-cells-retain-coefficients
kind: claim
title: Amenable compression cells over any hyperlinear base retain every base coefficient and packet trace, without residual finiteness
distinct_from:
  rf-amenable-two-cell-retains-coefficient: that needs a residually finite base and finite regular quotients separating the coefficient supports; this uses one canonical hyperlinear microstate of the base, so it applies to non-residually-finite bases such as EL_r of the Toeplitz ring, whose packet centre lies in the finite residual.
  rf-hnn-telescope-retains-coefficient-residual: that is the one-letter residually finite case; this is the multi-letter amenable case over an arbitrary hyperlinear base.
  amenable-multi-compressors-have-a-joint-hs-telescope: that telescopes one fixed exact finite-dimensional representation; this telescopes an approximate canonical microstate and computes the retained coefficient norms and packet traces.
  ascending-hnn-cannot-create-nonhyperlinearity: that proves hyperlinearity of a single ascending HNN extension by permanence; this gives explicit coefficient-retaining covariance microstates for every right-Følner compression semigroup, including semigroup relations, with no Ore embedding needed.
---

**ESTABLISHED.**  Let `Lambda` be a hyperlinear group.  Let `P` be a
finitely generated right-cancellative semigroup with finite right Følner sets
`F_n`, generating set `A`, and

```text
alpha:P->End(Lambda),   alpha_(pq)=alpha_p o alpha_q,  every alpha_p injective. (HBA1)
```

Fix a finite window `W subset Lambda` and a coefficient `b in C[Lambda]`.
There are dimensions `D_n`, maps `Pi_n:Lambda->U(D_n)` and unitaries
`T_(n,s)`, `s in A`, such that for all `g,h in W`, all `s in A`, and every
fixed pair of stable-letter words equal in `P`:

```text
||Pi_n(gh)-Pi_n(g)Pi_n(h)||_2 -> 0,
tr Pi_n(g) -> tau_Lambda(g),                               (HBA2)
||Pi_n(b)||_2 -> ||lambda_Lambda(b)||_2,                   (HBA3)
T_(n,s) Pi_n(g) T_(n,s)^(-1) = Pi_n(alpha_s(g)) on all but a
   |F_n s triangle F_n|/|F_n| fraction of coordinates,     (HBA4)
```

and every fixed semigroup relation between stable-letter words has
normalized-HS defect tending to zero.

In particular, for any finite packet `B<Lambda` and projection
`z in C[B]`, `tr Pi_n(z)->tau_B(z)`; and for the bounded-type coefficient of
`one-bounded-type-coefficient-separates-unbounded-exits`,
`||Pi_n(z(1-a))||_2 -> ||lambda_Lambda(z(1-a))||_2 >= (1-epsilon) sqrt(tau_B(z))`.

**Contrapositive (the class obstruction).**  Suppose a finite cell over
`Lambda` consists of covariance rows for the generators of an amenable
right-cancellative compression semigroup, fixed semigroup relations, and
finitely many relators of `Lambda`, and suppose it pays a coefficient
`b` with `lambda_Lambda(b)!=0` by word energy, meaning
`||b(U)||_2 <= Phi(E_cell(U)) + o(1)` on all normalized-HS microstates of
growing windows with `Phi(0+)=0`.  Then `Lambda` is not hyperlinear.  So
such a cell cannot supply the first non-hyperlinear group: it can only
restate non-hyperlinearity of its base.  Residual finiteness of the base
plays no role.

DERIVATION
hyperlinear-base-amenable-telescope-proof
