---
rg: 2
id: type-filtered-wandering-moments-sum-rejection-mass
kind: claim
title: Finitely many type-filtered wandering moments charge the whole rejection mass
distinct_from:
  exhaustive-marked-type-energy-summation: that sums compressed relator energy over orthogonal type domains; this sums canonical-trace moments filtered by finite group-algebra idempotents.
  central-marked-swap-star-has-two-word-trace-floor: that uses the central Fourier filter `(1-y)/2` for one binary swap star; this permits every primitive marked-type filter and the nonlinear forbidden spectral projection.
  algebraic-exhaustive-marked-type-detectors-violate-induction: that blocks exact relator domination on every type; the wandering moments here are required only in finite matrix microstates and are allowed to fail in induced infinite representations.
---

Let `H` be a fixed finite context packet, let `q_lambda in C[H]` be the
primitive central idempotent of a marked irreducible `lambda`, and let `F`
be the forbidden selector projection for the context.  Assume `F` commutes
with `q_lambda` and put

```text
P_lambda=q_lambda F.                                  (TFW1)
```

For every marked `lambda`, suppose there is an ordinary group word
`r_lambda` and a constant `c_lambda>0` such that finite-dimensional canonical
microstates satisfy

```text
Re tr(P_lambda(U) r_lambda(U))
 >=c_lambda tr(P_lambda(U))-omega_lambda(delta).      (TFW2)
```

Also suppose that every group word

```text
g r_lambda,      g in supp(P_lambda),                 (TFW3)
```

is nonidentity whenever its coefficient in the group-algebra expansion of
`P_lambda` is nonzero.

Then canonical microstates force

```text
tr(P_lambda(U))->0                                    (TFW4)
```

for every marked type.  Since there are only finitely many types and
contexts, the sum of all forbidden masses tends to zero.

## Proof

Write

```text
P_lambda=sum_(g in H) a_(lambda,g) g.                 (TFW5)
```

The sum is fixed and finite.  By `(TFW3)`, canonical trace separation gives

```text
tr(P_lambda(U)r_lambda(U))
 =sum_g a_(lambda,g)tr(g(U)r_lambda(U))->0.            (TFW6)
```

Insert `(TFW6)` in `(TFW2)` and use `c_lambda>0`.  This proves `(TFW4)`.
Taking the minimum of the finitely many constants and summing the finitely
many moduli is harmless.

If the literal common-variable consistency rows have vanishing energy, the
static finite-game gap gives

```text
sum_(contexts c) sum_(marked lambda)
 tr(P_(c,lambda)) >= gamma tr(Q)-o(1),                 (TFW7)
```

where `Q` is the common D8 source and `gamma>0`.  Equations `(TFW4)--(TFW7)`
force `tr(Q)->0`.  A canonical microstate of a nontrivial central mark has
`tr(Q)` bounded below, yielding non-hyperlinearity.

No primitive idempotent is asserted to be a group word.  It is used only as
a finite Fourier linear combination in the proof of `(TFW6)`; the actual
canonical tests are the finitely many ordinary words in `(TFW3)`.
