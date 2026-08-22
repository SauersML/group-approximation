---
rg: 2
id: correlated-haar-onehot-dichotomy-proof
kind: route
title: Count linear-code selector marginals and disintegrate the nonlinear Haar corner
target: correlated-haar-onehot-dichotomy
requires: []
---

The pushforward of Haar measure under the continuous homomorphism `pi_F` is
uniform measure on the finite vector space `K_F`.  This proves `(CHO1)`.
Since `H_Q^F` has `m^|F|` points and `|K_F|=p^r_F`, intersection counting
gives `(CHO2)`.  The exponential statement follows immediately.  On the
other hand the diagonal code

```text
{(v,v,...,v):v in F_p^Q}
```

has relative block distance one while its all-one-hot density is
`m/p^m`, independent of `|F|`.  Hence neither minimum distance nor an LDPC
presentation changes the relevant statistic; marginal rank does.

We next classify affine subsets of the one-hot alphabet.  Let
`A=x+V subset H_Q`.  If `p=2` and `A` contained three distinct basis vectors
`e_i,e_j,e_k`, affine closure would also contain
`e_i+e_j+e_k`, which is not one-hot.  Thus `|A|<=2`.  If `p` is odd and `A`
contained distinct `e_i,e_j`, its affine line would contain

```text
e_i+2(e_j-e_i) = 2e_j-e_i,
```

which is not a basis vector, so `|A|=1`.  Every coordinate marginal of an
affine-Haar process is affine Haar on the image coset.  If that process is
supported on `H_Q^I`, the displayed classification applies at every
coordinate and proves the first alternative.

For the second alternative, invariance of `Y` gives
`u_g z u_g^*=z` for all `g in Lambda`; since `z` lies in the abelian base it
is central in `M`.  Compressing the algebraic crossed product by an invariant
set is exactly the crossed product of the restricted probability action,
with the normalized corner trace.  This proves `(CHO3)`.  Connes embeddability
passes to von Neumann subalgebras and corners, so non-CE of `zMz` implies
non-CE of `M`.  Fourier transform identifies
`M=L(K-hat rtimes Lambda)`, proving the asserted non-hyperlinear conclusion.

Finally suppose the selector map `sigma:Y->Omega` is equivariant and `Omega`
is finite.  Decompose `Omega` into orbits.  On a transitive orbit choose
`omega_0`, representatives `r_i` for its points, and let
`p_i=1_{sigma^(-1)(r_i omega_0)}`.  The usual transformation-groupoid matrix
units transport the fibers to the base fiber, while

```text
p_0(zMz)p_0 = L^infinity(Y_omega0) rtimes Stab_Lambda(omega_0).
```

They give the matrix amplification in `(CHO4)`; summing over finite orbits
gives the direct sum.  Matrix amplification and finite direct sums preserve
Connes embeddability.  Therefore a non-CE finite-image selector corner forces
a non-CE stabilizer fiber action.  Point fibers recover the earlier finite
one-hot stabilizer reduction, while an infinite image is precisely the
unresolved nonlinear algebraic-envelope case.

