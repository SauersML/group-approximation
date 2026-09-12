# STW XXII: diffuse spectral-capture and Stiefel filling audit

## Result

For every `2`-norm-continuous loop `x:S^1->Nq` in a `II_1` factor with
`sup||x||_2<=delta`, there is a continuous constant-trace projection carrier
`e_z<=q` such that

```text
tau(e_z)<67 delta^2/kappa^2,
||x(z)(q-e_z)||<=kappa.
```

This closes the diffuse projection-weight hinge. For separable `II_1`
factors it gives the same universal quadratic small-loop filling modulus as
the matrix proof:

```text
rho_St(epsilon)=min(epsilon,1)^2/2560.
```

## Checks on the summable-carrier construction

1. Operator-norm-continuous loops are dense in continuous loops for the
   uniform `2`-metric: use fine cyclic partitions and affine interpolation.
2. The successive approximation errors are `delta 4^(-j)`, while the
   operator residual budgets are `kappa 2^(-j)`. Consequently the carrier
   traces are summable, with exact total bound `200/3<67` times
   `delta^2/kappa^2`.
3. Carriers are added orthogonally in the complement of all earlier
   carriers. Raw joins of moving spectral projections are never taken.
4. At each finite stage the carrier is operator-norm continuous. The
   increasing limit is uniformly `2`-continuous because its squared tail
   norm is the scalar tail sum of the allocated traces.
5. On the final complement every increment has operator norm at most its
   assigned residual. Their series therefore converges in operator norm.
   Its partial sums also converge in `2`-norm to the original loop, which
   identifies the operator limit with the desired compression.

## Checks on the norm-continuous patch

At each arc centre, the hard spectral projection above `alpha/2` has trace
at most `4D^2/alpha^2`. It is enlarged locally to that fixed trace. Global
carriers have twice that trace. During a transition, one fixed carrier
contains both adjacent local carriers; the first half of the transition
retains the first carrier and the second half retains the second. Thus the
patch is continuous and always has a valid local spectral cut, without any
claim that a moving join is continuous.

## Topological input after localization

The localized defect loop is lifted, in two one-dimensional selection
steps, to unitary loops in finite-factor corners. Jekel's contraction fills
those loops. The contraction is not assumed Lipschitz or radius preserving:
every projected frame throughout the contraction differs from the base only
on a projection of the fixed captured trace, which supplies the metric
bound automatically.

## Trust boundary

Jekel's stated theorem assumes separable predual, so the Stiefel consequence
is recorded under that hypothesis. The spectral-capture lemma itself does
not use separability. The arbitrary-positive-weight multicopy transfer in a
diffuse factor is not asserted here; it also requires a relative
low-spectrum extension in the moving complement of a high-frame filling.
