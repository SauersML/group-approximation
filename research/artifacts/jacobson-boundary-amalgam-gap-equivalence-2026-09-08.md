# The exact finite-amalgam gap and marked corona collapse

2026-09-08. This identifies the remaining matrix obstruction for the
stronger boundary presentation. It does not assert positivity of the
infimum. The earlier two-braid infimum remains zero.

Use the finite groups, common subgroup, and specified embeddings of
[the relative-rounding proof](jacobson-boundary-packet-relative-rounding-2026-09-08.md):

```text
F=GL_3(F_2)_Q x GL_3(F_2)_P,
J=Hom(F_2^2,F_2^3) semidirect (K_Q x G_*),
L'=P_Q x K_P,
Xi=< F *_(L') J | (h b)^3=1, W=1 >,
w_Q=x_13,Q.
```

The words `b,W` have exactly the definitions in
[the first-level reconstruction](jacobson-ts-splitting-and-first-level-root-packet-2026-09-08.md).
In particular `h` is an element of `J`, and every occurrence of it
in the two words uses this one element. The literal Jacobson action
gives a homomorphism from `Xi` retaining `w_Q`, so `w_Q!=1` in
`Xi`. Finite multiplication tables for `F,J`, the common subgroup
identifications, and the two mixed relators specify a finite
presentation.

For every pair of exact unitary representations on the same dimension,

```text
rho_F:F->U(d), rho_J:J->U(d),
rho_F|L'=rho_J|L', rho_F(w_Q)!=I,
H=rho_J(h),
```

evaluate the two mixed words in these matrices. Define

```text
gamma_Xi=inf max(||(H rho_F(b))^3-I||, ||W-I||),
```

where the infimum ranges over all such pairs and all positive integers
`d`. Then

```text
0<=gamma_Xi<=2,

gamma_Xi>0
  iff every homomorphism Xi->U(product M_(d_n)/directSum M_(d_n))
      kills w_Q.
```

The direct sum here consists of sequences tending to zero in operator
norm. The equivalence concerns this specified mark; zero gap does not
assert that `Xi` embeds into a corona or that `Xi` is MF.

## Nonempty domain

Choose a common multiple `m` of `|F|` and `|J|`. Let each factor
act on `m` points by copies of its left regular action. Each restricted
`L'`-action is free and has `m/|L'|` orbits. Relabel the second
set by an equivariant bijection of these free `L'`-sets. The two
faithful permutation representations now agree on `L'`, and their
complex permutation representations belong to the domain of the
infimum. Every word is unitary, so both distances are at most two.
This proves the asserted bounds. These factor representations are not
asserted to satisfy either mixed relator.

## Zero gap gives a marked corona map

Choose a sequence of admissible pairs whose maximum mixed error tends
to zero. They already give exact representations of the amalgam in
each coordinate. Passing to the norm corona makes the two mixed words
the identity, giving a homomorphism from `Xi`.

The matrix `rho_F(w_Q)` is a nonidentity involution in every
coordinate. Therefore its distance from the identity is exactly two.
Its corona class has distance two from the identity, so the mark
survives.

## A marked corona map gives zero gap

Conversely suppose a homomorphism from `Xi` to such a corona retains
`w_Q`. Lift the finitely many values of `F` and `J` to unitary
matrix sequences, taking the identity to the identity. Such lifts
exist: any representative of a unitary class is eventually invertible
and asymptotically unitary, so its polar unitary differs by a sequence
tending to zero.

The finite multiplication tables imply that the maximum
multiplicativity defect within either factor tends to zero. The
finite-group correction lemma in the relative-rounding proof, applied
with trivial subgroup, gives exact representations `alpha_n` of `F`
and `beta_n` of `J` on the original dimensions, asymptotically close
to the chosen lifts. Their restrictions to `L'` are asymptotically
close because the two restrictions represent the same corona elements.

For all sufficiently large `n`, form

```text
T_n=|L'|^(-1) sum_(l in L') alpha_n(l) beta_n(l)^*.
```

Its distance from the identity tends to zero, so it is invertible.
The identity `alpha_n(l) T_n=T_n beta_n(l)` makes its unitary
polar factor `U_n` an intertwiner of the same representations.
Moreover `||U_n-I||` tends to zero. Replacing the entire second
representation by `U_n beta_n U_n^*` makes its restriction exactly
`alpha_n|L'`, without changing the first representation. Conjugating
the whole factor preserves all its word identities, including every
occurrence of `h`.

The mixed errors still tend to zero, because they are fixed finite
words and all corrections tend to zero in operator norm. The exact
involutions `alpha_n(w_Q)` represent the original nonidentity corona
element. Infinitely many must be nonidentity; otherwise that element
would be the identity. Restrict to those coordinates. This gives a
sequence in the defining domain of `gamma_Xi` with errors tending
to zero, as required.

## Consequence and remaining requirement

Strict positivity would make the literal nontrivial mark invisible in
every matrix norm corona, and therefore prove that the explicit group
`Xi` is non-MF. The argument uses only finite-group averaging, polar
decomposition, and fixed-word norm estimates.

The reconstructed first-level finite subgroup is a necessary
consequence of exact mixed relations. It does not prove the required
positive lower bound in arbitrary dimensions. That lower bound remains
the open premise of this route.
