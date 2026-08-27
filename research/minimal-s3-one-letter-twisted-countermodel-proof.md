---
rg: 2
id: minimal-s3-one-letter-twisted-countermodel-proof
kind: route
title: Retain the Schur center in finite quotients and compress amenable twisted regular representations
target: minimal-s3-one-letter-actors-have-twisted-countermodels
requires:
  - agent-aggregate-escape-two-intertwiner-clifford-dichotomy
  - virtually-free-full-algebras-are-rfd
  - finite-s3-cross-edge-holonomy-cannot-renew-saturated-escape
---

The relations in `(MST1)` give `S_3 x Z`.  Since `u` acts trivially on the
packet, the stabilizer is `A_sigma x Z`.  The packet cocycle is inflated from
the finite group `A_sigma`; take its inverse twisted regular representation
and let `u` act by any scalar.  This is already an exact finite-dimensional
inverse-projective stabilizer representation.

The group in `(MST2)` is virtually free.  The action map to `S_3` has finite
image, so the preimage of `A_sigma` has finite index and is virtually free.
More generally, a finite graph of finite groups is virtually free, as is
every finite-index subgroup.  The packet cocycle is finite-valued after the
finite Schur-cover normalization.  Its ordinary central extension

```text
1 -> mu_m -> E_sigma -> Q_sigma -> 1                  (1)
```

is a finite extension of a virtually free group and is therefore virtually
free.  In particular it is residually finite.  Choose a finite quotient of
`E_sigma` injective on the finite central subgroup `mu_m`.  In the quotient
regular representation, restriction to `mu_m` is a positive multiple of its
regular representation, so every central character occurs.  Cutting by the
inverse packet character produces a nonzero finite-dimensional
inverse-projective representation of `Q_sigma` satisfying all its relations.

By the Clifford construction, tensor this multiplicity representation with
the packet implementers and induce over the finite packet-type orbit.  The
cocycles cancel, every full actor relation is exact, and the identity-coset
block contains `sigma` with fixed positive normalized density.  This proves
the exact claims.

Now assume only that `Q_sigma` is amenable.  Its finite central extension in
`(1)` is amenable.  The group von Neumann algebra of an amenable group is
hyperfinite; its finite central-character corner is exactly
`L_(omega^(-1))(Q_sigma)`.  Hence the twisted regular trace has matrix
microstates.  The same fixed packet tensor and finite-orbit induction turn
them into approximate full-cell representations, with defects tending to
zero and positive active density.

If an indefinitely reusable recurrence

```text
lambda a_n<=a_(n+1)+C p(n)sqrt(E),       lambda>1       (2)
```

held for these microstates, iteration and division by `lambda^N` would give

```text
a_0<=lambda^(-N)
   +C sqrt(E) sum_(j=0)^(N-1)lambda^(-1-j)p(j).         (3)
```

Letting `N` tend to infinity and then the microstate defect tend to zero
would force `a_0` to zero, contrary to the fixed active density.  Thus an
amenable active stabilizer cannot support the required recurrence.  This is
an explicit twisted-regular countermodel argument, not an invocation of the
existential twisted-factor equivalence.
