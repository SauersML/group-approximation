# Diagonal-covariant Pauli incidence and the constant-depth boundary

## Exact finite word template

Let `c=tU^(-1)`.  For each base Toeplitz Pauli seed `a` and each base
Fanizza selector/reset word `z`, impose

```text
[t,U]=[U,a]=[c,z]=[z,a]=1.                              (A1)
```

Writing `a_i=t^i a t^(-i)` and `z_j=U^j z U^(-j)`, one has

```text
a_i=c^i a c^(-i),        [U,a_i]=[z_j,a_i]=1.           (A2)
```

The calculation is entirely internal to ordinary group words.  It uses no
identification `t=U`, no projection-valued relation, and no controlled
automorphism.  Its derivation area is polynomial in the addresses by
commutator collection and the existing quadratic diagonal-covariance
estimate.

The tensor assignment

```text
t=T tensor U_B,    U=I tensor U_B,    c=T tensor I,
a=a_T tensor I,    z=I tensor z_B                            (A3)
```

is an exact model of `(A1)`.  Hence the construction preserves the Toeplitz
height and every marked nontrivial BCS word.  Translation-symmetrized reset
generators may simply be included in the finite `z` menu.

If the Fanizza support projections `E,H` are built from this shifted menu,
they commute with all addressed old-spin Paulis.  The native chord `U` does
as well.  Consequently the coordinate-Pauli square-function estimate applies
directly to `q=E-((E-H)UE)^*((E-H)UE)` after fixed packet exactification.

## Constant-depth bypass

At fixed depth `m`, the same conclusion is even more direct: name all
coordinate Paulis and all chords, and impose every required commutator.  The
presentation is still finite, its exactification constant may depend on
`m`, and a properly infinite multiplicity factor realizes all finite packet
and Morita sizes simultaneously.  This bypasses both clocks.

What it does not produce is a strict comparison of successive multiplicity
currents.  The Schur child Morita wire reconstructs both transverse child
charts and therefore conserves their combined multiplicity.  Commutation
localizes a Gram but does not force that Gram to be full, does not select one
child, and does not make inactive mass pay.  A finite packet-only strict
contraction is refuted by its negative regular stationary summand.

Thus the same-carrier incidence row is solved, but the constant-depth lift
still needs a joint infinite-ambient, amplification-stable one-sided child
payment with positive normalized-HS density.
