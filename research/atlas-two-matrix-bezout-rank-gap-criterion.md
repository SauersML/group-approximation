---
rg: 2
id: atlas-two-matrix-bezout-rank-gap-criterion
kind: claim
title: A finite Bezout certificate in the two-matrix Atlas quotient gives a uniform rank gap
distinct_from:
  atlas-square-root-bridge-two-matrix-rank-reduction: that constructs the thirteen explicit matrix-valued polynomials; this identifies the exact algebraic certificate which rules out their asymptotic matrix zeros.
  atlas-augmented-relator-ideal-not-left-finite: that concerns the full group-algebra kernel and rules out finite left generation there; this uses a restricted two-generator quotient and permits two-sided polynomial multipliers.
  atlas-rank-stability-literature-fence: that audits correction theorems for the full Atlas presentation; this needs no stability theorem, only a finite ideal certificate in one explicit quotient algebra.
---

ESTABLISHED.  Let `p_1,...,p_N in F2<x,y>` be all scalar block entries of
the thirteen matrix-valued polynomials `P_w(X,Y)` from
`atlas-square-root-bridge-two-matrix-rank-reduction`, and put

```text
B=F2<x,y>/<p_1,...,p_N>.                              (BZR1)
```

If there is a finite noncommutative Bezout certificate

```text
1=sum_(j=1)^L a_j p_(i_j) b_j                        (BZR2)
```

in the free algebra, then every pair `X,Y in M_s(F2)` satisfies

```text
s <= sum_(j=1)^L rank p_(i_j)(X,Y)
  <= L sum_(w in R_13) rank P_w(X,Y).                 (BZR3)
```

In particular

```text
max_(w in R_13) rank P_w(X,Y)/s >= 1/(13L),           (BZR4)
```

so the square-root bridge countermodel is impossible.  The multipliers in
`(BZR2)` may have arbitrary fixed degree and norm: matrix rank is unchanged
or decreased by left and right multiplication, so no analytic coefficient
bound is needed.

More generally, a sequence with

```text
rank P_w(X_s,Y_s)/s ->0  for every w                 (BZR5)
```

induces a unital homomorphism

```text
B -> product_rank M_(s)(F2),                          (BZR6)
```

where the target is the normalized-rank metric ultraproduct.  This target is
von Neumann regular and stably finite.  Thus the necessary algebraic object
is not merely a nonzero formal quotient `B`: it is a nonzero **stably finite
rank-ultraproduct quotient** of `B`.  Proving that `B` has no such unital
quotient also rules out `(BZR5)`, even when `1` is not visibly in the
ordinary two-sided ideal.

### Proof

Evaluate `(BZR2)` at `X,Y`.  Rank subadditivity and
`rank(APB)<=rank P` give

```text
s=rank I_s
 <=sum_j rank(a_j(X,Y)p_(i_j)(X,Y)b_j(X,Y))
 <=sum_j rank p_(i_j)(X,Y),                           (BZR7)
```

which proves `(BZR3)` and `(BZR4)`.  Under `(BZR5)`, evaluation of the free
algebra in the matrix sequence is multiplicative before passing to the
ultraproduct, while every defining `p_i` has rank zero there.  It therefore
factors unitally through `B`, proving `(BZR6)`.  Stable finiteness of a rank
metric matrix ultraproduct follows coordinatewise from equality of the ranks
of `I-AB` and `I-BA` (or from its standard continuous-regular-ring model).

The full-generation condition on `X_s,Y_s` is deliberately absent from the
certificate.  Matrix generation has no fixed dimension-independent bounded
word witness: Burnside spanning requires up to `s^2` independent words.
Therefore a finite Bezout audit can prove an unconditional rank gap, but one
cannot encode the surviving full-generation face by simply adjoining one
fixed polynomial claimed to mean “`X,Y` generate `M_s`.”

For the particular triangular frame used here, the certificate has now been
found.  `atlas-square-root-frame-has-unit-packet-residual` identifies one
`H18` packet edge whose residual is the fixed transvection `b-I`, independent
of `X,Y`.  One scalar entry is exactly `1`, so `(BZR2)` holds with `L=1` and
the quotient `(BZR1)` is zero.  Thus this entire square-root frame is closed;
the general criterion remains useful for other genuinely nonstationary
gauges.
