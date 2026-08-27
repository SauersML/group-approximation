---
rg: 2
id: full-support-factor-refutes-exact-exhaustive-typed-cap-chain
kind: claim
title: A full-support factor refutes every exact exhaustive typed cap chain
distinct_from:
  full-support-factor-forbids-cap-ranged-common-source-covariance: that starts with the common partial isometries; this shows that an exhaustive product of typed contractions plus telescoping local rows necessarily constructs them.
  sequential-overlap-polar-aligns-carriers-not-contexts: that obtains the common source from one positive profile and leaves covariance open; this proves that covariance cannot be supplied by representation-universal exact typed rows while retaining the full-support witness.
  universal-residual-wordization-collapses-carrier: that uses the faithful regular trace to rule out a universal residual lower bound; this uses the intended full-support perfect factor and rules out an exact exhaustive cap-chain implementation even when its products are nonzero.
---

**ESTABLISHED EXACT-COMPLETENESS NO-GO.**  Let `(M,tau)` be the
full-support perfect factor in
`full-support-factor-forbids-cap-ranged-common-source-covariance`, generated
by the global Boolean involutions `B_x`.  For every context `c`, choose a
proper cap projection `q_(c,lambda_c)` in an exact extension `N`.

Suppose a finite typed-chain gadget has finitely many profiles `lambda` and,
for every profile, contractions `Y_(c,lambda)` such that

```text
Y_(c,lambda)^*Y_(c,lambda)>=Y_(m,lambda)^*Y_(m,lambda),
range(Y_(c,lambda))<=q_(c,lambda_c).                  (ETC1)
```

Assume its fixed exhaustive lower bound remains true in the full-support
perfect representation:

```text
sum_lambda ||Y_(m,lambda)||_2^2>=a>0.                 (ETC2)
```

Finally assume the gadget's local ordinary rows telescope, at zero row
defect, to the raw prefix covariance required after thresholding a nonzero
profile.  Thus, if

```text
P=1_[epsilon,1](Y_(m,lambda)^*Y_(m,lambda)),
```

then

```text
A_(c,x)Y_(c,lambda)P=Y_(c,lambda)PB_x.               (ETC3)
```

for every context incidence.  Then these conditions are inconsistent.

Indeed `(ETC2)` gives a profile with nonzero final product.  Threshold a
nonzero spectral projection `P` of
`Y_(m,lambda)^*Y_(m,lambda)`.  Condition `(ETC1)` makes every prefix bounded
below on `P`; polar correction gives partial isometries `S_c` with one
common initial projection `P` and ranges below the selected proper cap
projections.  Zero covariance in `(ETC3)` passes through polar correction,
so

```text
A_(c,x)S_c=S_cB_x.
```

This is exactly the configuration forbidden by
`full-support-factor-forbids-cap-ranged-common-source-covariance`.

Thus an exhaustive typed cap chain cannot simultaneously have a
representation-universal positive product bound, exact ordinary local
covariance rows, and the supplied full-support perfect exact model.  A live
chain must make either its lower bound or its covariance payment genuinely
finite-matrix/canonical-type-only, or replace the perfect trace by one which
is already cap-supported.

## The smallest normalized Fano chain

The obstruction already applies to the most natural candidate.  For the
seven Fano maximal-cap projections one has

```text
sum_lambda q_(c,lambda)=4I.
```

Put `T_(c,lambda)=q_(c,lambda)/2` and

```text
Y_(c,lambda)=T_(c,lambda_c)...T_(1,lambda_1).
```

Then the row Parseval identity

```text
sum_lambda T_(c,lambda)^*T_(c,lambda)=I
```

iterates to

```text
sum_(lambda_1,...,lambda_m)
  ||Y_(m,lambda)||_2^2=1.                             (ETC4)
```

For typed observables `B_(c,x)`, define

```text
D_(c,x,lambda_c)
 =B_(c,x)T_(c,lambda_c)-T_(c,lambda_c)B_(c-1,x).      (ETC5)
```

Ordinary multiplication gives the exact telescoping identity

```text
B_(m,x)Y_m-Y_mB_(0,x)
 =sum_c T_m...T_(c+1) D_(c,x,lambda_c)
          T_(c-1)...T_1.                             (ETC6)
```

All factors are contractions, so the resulting HS estimate has a fixed
constant depending only on the finite number of contexts.  Hence neither
mass nor telescoping is missing from this candidate.  What fails is exact
completeness: `(ETC5)` must be imposed for `x` through every layer, including
contexts not containing `x`.  Those are precisely the extra covariance rows
which the full-support model need not satisfy, and if it did satisfy all of
them then the full product would intertwine every `B_x`; its Gram projection
and spectral cuts would commute with every `B_x`, `(ETC3)` would follow, and
the preceding no-go would apply.

Already in `M_2`, take

```text
q=(I+X)/2,     B=Z.
```

Then `q` is a full-support binary-context atom and

```text
||Bq-qB||_2^2=1.
```

Thus a chain layer belonging to the `X` context cannot transparently carry
the unrelated `Z` variable.  Omitting that nonincidence row leaves the
uncancelled commutator in `(ETC6)`; adding it destroys this exact model.
Variable-star chains avoid the row, but then their source projections depend
on the variable star and do not give the one common source required by the
game decoder.
