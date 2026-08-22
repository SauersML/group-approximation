# The reset scalar ray carries a sharp compressed-Gram spectator

## Construction

Take one exact label representation `rho` of the finite full reset on `V`.
Let `H_0<=E_0` have ranks `s<r`, with `s/dim(V)=1/8`, and amplify by
`C^N`.  Choose `N` so that `sN/r` is an integer and a projection

```text
Q in M_N(C),              rank(Q)=sN/r.
```

Set

```text
E=E_0 tensor I,       H=H_0 tensor I,
F=E-H,                q=E_0 tensor Q.                    (A1)
```

The source space after removing `q` and the guarded target have equal rank:

```text
rank(E-q)=rN-sN=(r-s)N=rank(F).                          (A2)
```

Choose a unitary, or a symmetry, `U` taking `Ran(E-q)` to `Ran(F)` and the
orthogonal complement to `Ran(F)^perp`.  For `X=FUE`,

```text
X^*X=E-q,
||X^*X-E||_2^2=tr(q)=s/dim(V)=tr(H)=1/8.                (A3)
```

This is not merely an arbitrary Reynolds spectator: it is the Gram
deficiency of the exact compressed chord, and it realizes equality in the
finite-dimensional guarded rank floor.

## Compatibility with the new inputs

The reset representation is `rho tensor I_N`, so its translation orbit,
branch flips, balanced child/full type vector, and scalar-ray conclusion are
all exact.  The finite label algebra is amplified by `I_N`, whereas
`q=E_0 tensor Q` uses a non-scalar residual projection and is outside that
algebra.

Add an independent Toeplitz old-spin factor.  All coordinate Paulis act
there, while `E,H,U` act on `V tensor C^N`.  Setting the diagonal stable
letter to `T tensor U` makes its difference from the chord equal to
`T tensor I`.  Hence the exact diagonal-difference incidence and every
addressed Pauli commutator hold.  Pauli localization sees no error because
`q` is already in the old-spin commutant.

## Boundary

The packet gap `gamma_A` quantizes nonzero projections only in the finite
label algebra.  Translation symmetry fixes the label multiplicity profile;
it does not act on or name the scalar multiplicity matrix algebra.  The
compressed chord can therefore spend exactly the rank forced by `H` inside
that anonymous factor.

Any closing relation must be mixed: it must couple the native chord to a
reset word in a way which is not invariant under arbitrary multiplicity
unitaries/projections.  Without that new relation, the rank floor,
coordinate-Pauli localization, finite label trace gap, diagonal incidence,
and complete translation reset are jointly consistent with `(A3)`.
