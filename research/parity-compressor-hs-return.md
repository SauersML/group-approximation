---
rg: 2
id: parity-compressor-hs-return
kind: claim
title: The Toeplitz parity compressor kills its mark in tracial matrix ultraproducts
---

For the explicit group `H_T` in `toeplitz-parity-compressor-candidate`, every
homomorphism

```text
pi:H_T -> U(prod_omega M_(d_n))
```

into a tracial matrix ultraproduct satisfies `pi(J)=1`.

This is the exact remaining normalized-Hilbert--Schmidt endpoint for the
parity candidate.  It is **OPEN**.  Property `(T)` by itself does not prove
it, and the operator-norm theorem
`kazhdan-asymptotic-commutant-transport` cannot be cited for this metric.

The endpoint has a useful equivalent obstruction picture.  If `pi(J)!=1`,
cut by the central negative projection

```text
P_-=(1-pi(J))/2.
```

On this corner put `e=(1+pi(q))/2`.  Then

```text
e in pi(alpha(Lambda))',
pi(p)e pi(p)^*=1-e                for every p with chi(p)=1. (PCR1)
```

Thus a countermodel is not allowed to hide the error in a small corner: for
the canonical group trace `tau(P_-)=1/2`, and inside that corner
`tau(e)=1/2` and `||pi(p)e pi(p)^*-e||_2=1`.  The only possible escape is a
macroscopic projection in the excess commutant

```text
pi(alpha(Lambda))' \ pi(Lambda)'.                            (PCR2)
```

Proving that this particular two-point excess projection cannot occur in a
tracial **matrix** ultraproduct would establish the claim.  The analogous
statement for arbitrary finite tracial von Neumann algebras is false: the
negative central corner of the left regular representation of `H_T` itself
realizes `(PCR1)`.

## Attempts

The direct finite-dimensional proof compares the dimensions of two conjugate
commutants.  It dies in a tracial ultraproduct because the corresponding
closed subspaces may be properly nested and unitarily conjugate.  Property
`(T)` does not repair this: it controls almost-invariant vectors for honest
unitary representations, whereas normalized-HS microstates can place the
missing direction in a non-coordinate excess commutant.  The live attack is
therefore narrower: exclude the specific macroscopic two-point projection
`(PCR1)`, using its finite spectrum and flip relation, without asserting full
commutant normalization.
