---
rg: 2
id: toeplitz-head-jacobi-words-give-uniform-expanders-proof
kind: route
title: Put each finite Jacobi parabolic into the Toeplitz head and Gaussian-eliminate its generators
target: toeplitz-head-jacobi-words-give-uniform-expanders
requires:
  - truncated-polynomial-binary-weyl-expander-tower
  - toeplitz-finite-head-centralizes-deep-tail
---

Let `V_n=R_n^2` with the symplectic form `(TPW1)`. Choose symplectic bases
recursively along the embeddings `(TPW2)`, so `V_n` is the first symplectic
summand of `V_(n+1)` and the complement is one hyperbolic plane. Use the
associated nested Pauli groups `P_n`, with their fixed order-four phase
center, common involution `J`, and one new Pauli pair at each step. Enlarging
the extraspecial Weyl group by this fixed phase center does not change its
`J=-1` spin dimension or adjoint commutant.

Let `Aut_0(P_n)` be the automorphisms fixing the phase center and let
`G_tilde_n` be the inverse image in `Aut_0(P_n)` of the symplectic image of
`EL_2(R_n)`. Put

```text
widehat(Jac)_n=P_n semidirect G_tilde_n.
```

Then conjugation gives exactly the required symplectic action on
`P_n/Z(P_n)`. Passing to the full inverse image rather than choosing a
possibly nonexistent splitting is necessary in characteristic two.

The groups `widehat(Jac)_n` have faithful characteristic-two representations
of dimension polynomial in `n`. One concrete model is their action on a
fixed-degree quotient of the modular Pauli augmentation algebra. Degree one
records `P_n/Z(P_n)`, degree two records the central commutators, and the
fixed finite phase center costs only a fixed number of further degrees and a
constant additional block. Pauli translations act by left multiplication and
the Clifford lifts act by algebra automorphisms. The action is faithful: a
noncentral Pauli element is detected in degree one, the marked center is
detected in degree two, the bounded phase center is detected in the fixed
auxiliary block, and a nontrivial symplectic image is detected on degree one.
Hence all data act on a binary space of dimension `M=poly(n)`.

Equivalently, this is the bounded-degree linearization of the finite
Clifford/Jacobi action on

```text
1 direct_sum V_n direct_sum (bounded tensor powers of V_n) direct_sum phase.
```

Under the recursively chosen bases, the Pauli subgroups are nested. Only the
level-dependent Clifford lifts need be represented separately; compatibility
between lift choices at different levels is not used.

By `(TFH1)`, a Toeplitz head of size `M=poly(n)` is `M_M(F_2)`. Stabilizing with
the fixed `r>=4` outer matrix coordinates embeds its elementary group
`EL_(rM)(F_2)` into `EL_r(T)`: a combined elementary matrix with distinct
outer coordinates is a root element with coefficient `e_(ij)`, while a
same-outer-coordinate elementary matrix is a commutator through one spare
outer coordinate. Since `F_2^x={1}`, every finite matrix used above lies in
the elementary group after this fixed stabilization.

Use the corresponding root words in `St_r(T)`. The Steinberg relations give
the same stabilized elementary calculus, and the projection to `EL_r(T)` is
faithful on each finite head group (equivalently, the finite-field head has no
extra unstable `K_2` ambiguity). Thus the finite Jacobi groups and their
nested Pauli subgroups lift as honest finite subgroups of the fixed Steinberg
group. Krstic--McCool finite presentation and the universal-lattice
property-`(T)` theorem apply because `T` is a finitely presented, finitely
generated unital associative ring and `r>=4`.

Each coefficient `e_(ij)=x^i(1+xy)y^j` has ring-word length `O(M)`. Gaussian
elimination writes an `M`-dimensional binary matrix as `O(M^2)` combined
elementary matrices. Replacing each by the preceding root word gives a word
in the fixed generators of `Gamma_T` of polynomial length in `n`. The same
elimination is an explicit polynomial sequence of Steinberg addition and
commutator identities, so it supplies polynomial derivations of all finite
Jacobi multiplication and conjugacy relations, not merely equality in the
ambient group.

Apply this to the fixed relative-Kazhdan word set from
`truncated-polynomial-binary-weyl-expander-tower`. Its images are the words
`g_(j,n)`. The abstract theorem already proves that their adjoint channel on
every irreducible `J=-1` spin block has a uniform gap. The embedding preserves
the exact action and the nested one-qubit inclusions, proving all four clauses.
