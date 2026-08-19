# The harmonic dual lattice does not require a primitive harmonic basis

Date: 2026-08-11

## Outcome

The exact harmonic dual systole and the order of each discriminant class can
be computed from **any** rational basis of the harmonic subspace.  One does
not need to construct the often-expensive primitive lattice

```text
K_H = H intersect Z^m.                                  (QSB1)
```

This removes the generic ambient integer-kernel/HNF calculation from the
projective screening pipeline.  The remaining integral calculation is the
pairing-image lattice in `rank(H)` variables.

## Coordinate theorem

Let `K subset Z^m` be an integral lattice, let `H subset span_R(K)` be a
rational subspace, and put

```text
Q^#={u in H:<u,k> in Z for every k in K}.              (QSB2)
```

Let the rows of a rational matrix `R in M_(r,m)(Q)` be any basis of `H`,
and let the rows of `C in M_(s,m)(Z)` be a basis of `K`.  Define

```text
P=R C^T in M_(r,s)(Q),
Lambda_P=span_Z{columns of P} subset Q^r.              (QSB3)
```

**Theorem 1 (span-basis reconstruction).**  The map

```text
Lambda_P^# -> Q^#,  x |-> xR                            (QSB4)
```

is an isometric lattice isomorphism when `Lambda_P^#` is equipped with the
pulled-back Gram form `R R^T`.

**Proof.**  Every `u in H` is uniquely `u=xR`.  Every `k in K` is `k=aC`
for an integral row `a`.  Therefore

```text
<u,k>=x R C^T a^T=x P a^T.                             (QSB5)
```

This is integral for every `a in Z^s` exactly when `x` pairs integrally
with every column of `P`, equivalently when `x in Lambda_P^#`.  Injectivity,
surjectivity, and the metric assertion follow immediately.  End proof.

The theorem is invariant under replacing `R` by `TR` for any
`T in GL_r(Q)`.  In particular, clearing the denominator of each row of a
rational nullspace basis gives an integral spanning basis suitable for exact
arithmetic; it need not generate `(QSB1)` primitively.

## Integral membership and class order without `K_H`

Assume now that `K_H` is exactly `(QSB1)`.  This is the projective harmonic
setup.  For `u in Q^#`,

```text
u in K_H  iff  every ambient coordinate of u is integral. (QSB6)
```

More generally, if the ambient coordinates of `u` are reduced rational
numbers, then

```text
ord(u+K_H)
 =lcm{denominator(u_j):1<=j<=m}.                       (QSB7)
```

**Proof.**  Because `u` already belongs to `H`, membership in
`H intersect Z^m` is precisely coordinatewise integrality.  The least
positive `n` for which `nu` is integral is the least common multiple of the
reduced coordinate denominators.  This is exactly the order in the quotient
`Q^#/K_H`.  End proof.

Thus the three quantities needed by the localized screen are all available
without a primitive basis of `K_H`:

1. `lambda_1(Q^#)` comes from exact SVP in the physical lattice `(QSB4)`;
2. harmless versus nonintegral is the coordinate test `(QSB6)`; and
3. the exact discriminant-class order is `(QSB7)`.

Smith invariants of the entire quotient still require a primitive basis, but
the localization theorem does not use them.

## Projective implementation

In `experiments/sl3_projective_cellular_harmonic_export.py`, the rational
harmonic nullspace is computed exactly and its row denominators are cleared.
In `experiments/sl3_projective_cellular_systole.py`, the columns of the
harmonic-cycle pairing matrix generate `Lambda_P`; its dual is mapped back
to ambient coordinates exactly as in `(QSB4)`.

At level `79`, replacing the primitive harmonic basis by this nonprimitive
span basis reproduces, field for field, the previous exact

```text
Q-sharp common denominator,
shortest squared norm,
shortest class order,
spherical threshold product,
safe/non-safe conclusion.                                  (QSB8)
```

The combined span export and exact systole computation took `36` seconds on
one MSI core.  The compact regression certificates are

```text
experiments/projective-cellular-p79-harmonic-span-regression.json
SHA-256 68330c1bace834e5397a77d6f862dd5d9f82123d8e3fdcd4e9d9970c98e443bd,

experiments/projective-cellular-p79-systole-span-regression.json
SHA-256 b731e2d463d2268a2845c2d38701b3a16736994b2a78742c7f99638a9104c47e.
```

The reduction is especially valuable at level `121`, where the harmonic
rank is seven and primitive ambient intersection was the dominant
exact-arithmetic cost.

## Scope

This is an exact computational reduction, not a lower bound for the systole.
It makes the family experiment fast enough to target the correct invariant;
the uniform TRUE theorem must still control every nonintegral class below the
spherical threshold and its paired integral lift.
