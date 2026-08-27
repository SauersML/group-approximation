---
rg: 2
id: sl3-arithmetic-double-finite-representations-fold
kind: claim
title: Every finite-dimensional representation of the SL3 arithmetic double folds its two vertex copies
distinct_from:
  exact-projective-codensity-has-a-uniform-trace-square-gap: that controls one auxiliary unitary against one exact representation of the ambient arithmetic group; this applies co-density to a block swap and collapses the entire fold kernel of an arithmetic amalgam.
  sl3-hnn-admits-no-amalgamated-free-haar-unitary: that is an open statement about regular-trace matrix ultraproduct models of the HNN group; this is an exact finite-dimensional theorem for the smaller symmetric arithmetic double.
---

Put

```text
C = SL_3(Z),       A = SL_3(Z[1/2]),       D = A *_C A,
```

and write `i_0,i_1:A->D` for the two vertex embeddings.  Every
finite-dimensional unitary representation `Pi:D->U(d)` satisfies

```text
Pi(i_0(a)) = Pi(i_1(a))       for every a in A.                 (ADF1)
```

Equivalently, every such representation factors through the fold map

```text
fold:D->A,        fold(i_0(a))=fold(i_1(a))=a.                  (ADF2)
```

Thus the whole normal closure of the fold kernel, not merely one marked
commutator, is invisible to exact finite-dimensional representations.

## Proof

Let `pi_j=Pi compose i_j`.  Since the two copies are amalgamated over `C`,
their restrictions to `C` are literally equal.  On `H direct_sum H` define

```text
rho(a)=diag(pi_0(a),pi_1(a)),
V(x,y)=(y,x).
```

Then `rho` is an exact finite-dimensional representation of `A` and
`V in rho(C)'`.  The pair `C<=A` is finite-dimensionally co-dense, as
recorded in the `SL_3` instance of
`exact-projective-codensity-has-a-uniform-trace-square-gap`; hence

```text
rho(C)' = rho(A)'.                                             (ADF3)
```

Therefore `V rho(a)=rho(a)V` for every `a in A`.  Comparing the two
off-diagonal blocks gives `pi_0(a)=pi_1(a)`, proving `(ADF1)`.

This argument uses exactness only once, in `(ADF3)`.  For approximate
representations, promoting the almost `C`-intertwining block swap to an
almost `A`-intertwiner is precisely the normalized-Hilbert--Schmidt
outlier problem; the theorem does not silently assert that promotion.

