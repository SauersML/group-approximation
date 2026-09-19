---
rg: 2
id: stw10-krein-milman-factorial-witness-proof
kind: route
title: Apply Krein-Milman to the amenable face and then pass to the exact GNS quotient
target: stw10-factorialize-amenable-nonqd-witnesses
requires:
  - directed-unions-preserve-trace-approximations
  - exact-gns-kernel-amenability-reduction
---

Start with an amenable non-QD trace on `A`.
`directed-unions-preserve-trace-approximations` supplies a separable unital
subalgebra `B subset A` whose restricted trace remains amenable and non-QD.

Let

```text
K = {amenable tracial states on B},
Q = {quasidiagonal tracial states on B}.
```

Both are weak-star closed.  For example, given a weak-star convergent net of
amenable traces and a finite test packet, first choose a trace in the net
which is close to the limit on that packet and then choose one of its u.c.p.
matrix models.  The trace errors add, while its Hilbert--Schmidt
multiplicative defects are unchanged.  The same finite-packet argument with
operator-norm defects proves weak-star closedness of `Q`.  Direct sums with
block multiplicities prove that `Q` is convex.  Brown's amenable-trace
theorem says additionally that `K` is a face of `T(B)`, so `K` is compact
and convex.

Suppose every extreme point of `K` belonged to `Q`.  Krein--Milman and
closed convexity of `Q` would give

```text
K = closure(conv(ext(K))) subset Q,                           (FW2)
```

contrary to the amenable non-QD trace already on `B`.  Hence there is
`sigma in ext(K) minus Q`.  Because `K` is a face of `T(B)`, every extreme
point of `K` is extreme in `T(B)`: any decomposition in `T(B)` first has
both endpoints forced into `K`, and then extremality in `K` makes it trivial.
The standard factor criterion for tracial states now says that
`pi_sigma(B)''` is a factor.  This proves the general reduction and `(FW2)`
proves its if-and-only-if formulation.

If `pi_sigma(B)''` were finite dimensional, it would be some `M_d`, and the
GNS homomorphism

```text
pi_sigma:B -> M_d
```

itself, repeated as a constant sequence, would be an exactly multiplicative
u.c.p. matrix model inducing `sigma`.  Thus `sigma` would be QD, a
contradiction.  This also proves the stated positive corollary.

Now assume the original `A` is exact.  Exactness passes to `B`.  For an
amenable trace on an exact (indeed locally reflexive) algebra, Brown's GNS
theorem makes `pi_sigma(B)''` hyperfinite.  It has separable predual because
`B` is separable, and the preceding paragraph excludes the finite-dimensional
factor case.  The uniqueness of the separable hyperfinite II1 factor gives

```text
pi_sigma(B)'' is isomorphic to R.                             (FW3)
```

Put `J=ker(pi_sigma)` and `C=B/J`.  Then `C` is separable, exact and unital,
and the induced trace `bar_sigma` is faithful.  The exact GNS-kernel descent
theorem makes `bar_sigma` amenable.  It cannot be QD, since QD of
`bar_sigma` would pull back along `B -> C` and make `sigma` QD.  Its GNS
closure is still the factor in `(FW3)`, proving `(FW1)` and the exact-class
equivalence.

**Trust boundary.**  Brown's facts that amenable traces form a face and that
an amenable trace on a locally reflexive algebra has hyperfinite GNS closure,
the extreme-trace/factor criterion, Krein--Milman, and uniqueness of `R` are
imported.  Weak-star closedness and convexity of the relevant matrix-model
trace classes, exclusion of finite-dimensional factors, and every reduction
step are proved above.  Amenability alone is deliberately not claimed to
make a nonexact GNS factor hyperfinite.
