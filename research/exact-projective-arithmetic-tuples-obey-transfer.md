---
rg: 2
id: exact-projective-arithmetic-tuples-obey-transfer
kind: claim
title: Exact projective arithmetic tuples obey dimension-free trace-square commutant transfer
distinct_from:
  projective-commutant-transfer-for-arithmetic-pair: that asks for a modulus on arbitrary approximate tuples; this proves the inequality when every presentation relator is scalar, with no requirement that those scalars lift to a trivial cocycle.
  exact-projective-codensity-has-a-uniform-trace-square-gap: that starts with an honest unitary representation; this starts with an arbitrary honest PU(d)-representation and applies the exact theorem to its adjoint representation on M_d.
  sl2-exact-projective-transfer-via-doubled-squeeze: that proves exact transfer for honest unitary representations of the rank-one pair; this removes arbitrary scalar presentation defects before invoking it.
---

Fix `n >= 2`, a prime `p`,

```text
Lambda=SL_n(Z) < Gamma=SL_n(Z[1/p]),
```

a finite presentation `Gamma=<X|R>`, a finite generating set `S` of
`Lambda`, and `h in Gamma`.  Let `kappa>0` be a uniform conjugation-gap
constant for the finite-dimensional representations of the pair.  Thus the
projection `Q_pi` onto `pi(Lambda)'=pi(Gamma)'` satisfies

```text
||X-Q_pi(X)||_2^2
 <= kappa^(-2) sum_(c in S)||pi(c)Xpi(c)^*-X||_2^2.    (EPA1)
```

Let `rho:X->U(d)` be any assignment for which every defining relator is a
scalar:

```text
rho(r) in T 1_d       for every r in R.                (EPA2)
```

Then, for every `U in U(d)`,

```text
e(U,rho(h)) <= (4/kappa^2) sum_(c in S) e(U,rho(c)).   (EPA3)
```

Here word values such as `rho(h)` and `rho(c)` may be computed from any
fixed presentation words.  Changing a word by a relator changes its value
only by a scalar and hence does not change the trace-square energy.

## Proof

Condition `(EPA2)` says exactly that the generator tuple defines a
homomorphism

```text
bar(rho):Gamma -> PU(d).
```

Consequently the projective representation has the honest adjoint lift

```text
beta(g)=Ad(rho(g)): M_d -> M_d                       (EPA4)
```

is a well-defined honest unitary representation of `Gamma` on the
`d^2`-dimensional normalized Hilbert--Schmidt space.  Apply
`codense-gap-controls-exact-projective-tuples` to `bar(rho)`.  Its proof
uses this adjoint lift, and identity `(CDG6)` turns the ordinary conjugation
displacement of `Ad(U)` into exactly twice the original trace-square energy,
giving `(EPA3)`.

For `n=2`, the required co-density and `kappa` are supplied by
`sl2-z-inverse-p-over-sl2-z-is-codense-tau-pair`; for `n>=3`, they are the
property-(T) and co-density inputs recorded in
`exact-projective-codensity-has-a-uniform-trace-square-gap`.
Thus arbitrary finite-dimensional scalar `2`-cocycles, including
non-liftable projective representations, are rigorously outside the open
sector of `projective-commutant-transfer-for-arithmetic-pair`.  A failure of
the latter must retain genuinely nonscalar adjoint relator defect.
