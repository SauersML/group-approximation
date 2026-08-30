---
rg: 2
id: stw82-split-af-is-one-multiplier-projection-problem
kind: claim
title: The arbitrary split-AF maximum formula is exactly the one-multiplier-projection problem
distinct_from:
  stw82-af-split-stage-centres-obey-maximum: that theorem proves the maximum formula when the finite-stage block units commute with the ideal; the present theorem removes matrix sizes and shows that the whole remaining split-AF problem is equivalent to adjoining one arbitrary multiplier projection.
  stw82-raw-two-cut-reuse-iff-quasidiagonal: that theorem characterizes orthogonalization of quasicentral complementary cuts; the multiplier projection here is exact and need not arise from a quasicentral approximate unit.
artifacts:
  - research/artifacts/stw82-multiplier-projection-reduction-audit-2026-08-30.md
---

The following four assertions are equivalent.

1. For every C*-algebra `A` and projection `p in M(A)`,

   ```text
   dim_nuc(A+C p)=dim_nuc(A).                            (MP1)
   ```

2. Every unital split extension with quotient `C direct_sum C` obeys the
   nuclear-dimension maximum formula.
3. Every unital split extension with finite-dimensional quotient obeys the
   nuclear-dimension maximum formula.
4. Every unital split extension with AF quotient admitting a dense directed
   union of unital finite-dimensional subalgebras obeys the
   nuclear-dimension maximum formula.

Thus the arbitrary split-AF case of STW Problem LXXXII is neither a
many-block nor a matrix-amplification problem.  Its exact unresolved core is
whether adjoining one multiplier projection can raise nuclear dimension.

More precisely, let

```text
0 -> I -> E -> direct_sum_(j=1)^k M_(r_j) -> 0          (MP2)
```

be unital and split.  Choosing lifted matrix units and one minimal
projection from each block produces a full corner `B=pEp` such that

```text
dim_nuc(B)=dim_nuc(E),
B=J+C e_1+...+C e_k,       J=pIp,                       (MP3)
```

where the `e_j` are orthogonal multiplier projections summing to the unit of
`B`.  Starting with `J_0=J` and setting

```text
J_m=J+C e_1+...+C e_m
```

adjoins exactly one multiplier projection at each step.  Conversely, after
unitization any nontrivial algebra `A+C p` is the middle algebra of a unital
split extension of `A` by `C direct_sum C`.  This proves the equivalence.

The Peirce decomposition also identifies exactly where the existing
stage-centre proof stops:

```text
[e_j,J]=0 for every j
  iff e_j J e_l=0 for every j!=l
  iff J=direct_sum_j e_j J e_j.                         (MP4)
```

If an off-diagonal corner is nonzero, a norm-one `x in e_j J e_l` satisfies
`[e_j,x]=x`.  Hence the canonical block projection is maximally noncentral,
not merely insufficiently close to central.  Formula `(MP4)` is an exact
no-go for extending the direct-sum stage-centre proof without a new argument
for multiplier-projection adjunction; it is not a counterexample to the
maximum formula itself.

There is an unconditional positive case beyond the central decomposition.
If `A` is sigma-unital and `p` is full on `A`, meaning

```text
closure(A p A)=A,                                      (MP5)
```

then `(MP1)` holds.  If `p in A`, the assertion is immediate.  Otherwise
`p` is a full projection of `A+C p`, and its corner is the minimal
unitization of the full hereditary algebra `pAp`.  Strong Morita invariance,
unitization invariance, and hereditary monotonicity give

```text
dim_nuc(A+C p)=dim_nuc((pAp)~)=dim_nuc(pAp)<=dim_nuc(A).
```

The reverse inequality is ideal monotonicity.  Consequently any failure of
the split-AF formula must pass through a nonfull multiplier projection.
