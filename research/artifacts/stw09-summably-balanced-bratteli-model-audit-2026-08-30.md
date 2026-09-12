# IX(2): summably balanced Bratteli models

## Result

The full-matrix rank obstruction shows that a viable trace-preserving
coherification cannot insist on normalized traces of simple matrix stages.
The replacement proved here uses genuine finite-dimensional Bratteli stages

```text
F_n=direct_sum_i M_(d_(n,i))
```

with arbitrary probability weight vectors `w_n` on their summands.

The connecting map is specified by a nonnegative integer multiplicity matrix
`M_n=(m_(j i))`.  It is a unital embedding exactly under the finite checks

```text
d_(n+1,j)=sum_i m_(j i)d_(n,i)     for every target summand j,
sum_j m_(j i)>0                    for every source summand i.
```

The induced pullback on trace weights is the explicit stochastic map

```text
(P_n v)_i=sum_j v_j m_(j i)d_(n,i)/d_(n+1,j).
```

Suppose quasidiagonal models into the `F_n` are summably norm-coherent along
these embeddings, asymptotically multiplicative, and converge to a faithful
trace `tau` under the stage traces represented by `w_n`.  The new point is
that the stage traces need not be exactly compatible.  It is enough that

```text
sum_n ||w_n-P_n w_(n+1)||_1 < infinity.
```

Then the models give a trace-preserving AF embedding.

## Trace-shadowing mechanism

For fixed `n`, pull the proposed weight at stage `m` all the way back:

```text
P_(n,m)w_m.
```

Successive pulled-back vectors differ by at most the imbalance at stage
`m`.  Summability makes them Cauchy.  Their limits `tilde_w_n` are exactly
compatible and satisfy

```text
||tilde_w_n-w_n||_1
 <= sum_(m>=n)||w_m-P_m w_(m+1)||_1 -> 0.
```

Replacing `w_n` by `tilde_w_n` therefore preserves convergence to `tau`.
The existing trace-coherent model criterion then constructs the AF limit
embedding, and faithfulness of `tau` proves injectivity.

This is not an inverse-limit surjectivity argument.  Trace restriction maps
between finite-dimensional stages need not be onto.  Exact compatible
weights arise from limits of arbitrarily late pullbacks.

## Relation to the irrational `C^2` obstruction

The prior obstruction applies when every `F_n` is a full matrix algebra with
its unique normalized trace.  Multi-summand stages have a trace simplex, so
irrational weights cause no problem.  For example, `C^2` with
`tau_lambda(a,b)=lambda a+(1-lambda)b` may be kept as the constant Bratteli
stage with weight vector `(lambda,1-lambda)` and identity connecting maps;
all coherence and balance errors are zero.

Thus the new theorem both avoids the normalized-rank obstruction and gives a
checkable sufficient hypothesis for IX(2).  It does not claim that every
faithful quasidiagonal trace admits such multiplicity matrices and summable
norm coherence; producing those data remains the open hinge.
