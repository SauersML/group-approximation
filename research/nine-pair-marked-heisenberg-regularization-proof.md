---
rg: 2
id: nine-pair-marked-heisenberg-regularization-proof
kind: route
title: Pair nine q-roots around the mark and compute the selector incidence
target: nine-pair-marked-heisenberg-regularization-is-selector-spectator
requires: []
---

For an elementary Steinberg root in characteristic two,
`x_ij(a)^2=1`.  Roots with a common initial index or a common terminal
index commute.  The only composable roots among `(NHR1)` are
`x_(1,k)(q)` and `x_(k,3)(q)`, and the Steinberg commutator rule gives

```text
[x_(1,k)(q),x_(l,3)(q)]
 =x_13(q^2) when k=l,
 =1           when k!=l.                              (NHRP1)
```

Since `q^2=q`, this is `(NHR2)`.  The marked root has the same initial
index as every `C_k` and the same terminal index as every `D_k`, so it is
central in the packet.

On `PH`, the relation `[C_k,D_k]=z=-1` says

```text
rho(D_k)rho(C_k)rho(D_k)^*=-rho(C_k),                 (NHRP2)
```

while `D_k` commutes with every `C_l`, `l!=k`.  Conjugation by `D_k`
therefore flips exactly the `k`-th sign in `(NHR3)`.  Products of the nine
`D_k` act transitively on the `2^9` joint sign projections.  Unitary
invariance of trace makes their traces equal, and their sum is `P`, proving
`(NHR4)`.

The same calculation proves `(NHR5)` without importing a representation
theorem.  For one pair, the four operators

```text
1, C_k, D_k, C_kD_k
```

obey the two-by-two Pauli multiplication table on `PH`, so their generated
unital star algebra is `M_2(C)`.  Different pairs commute.  Tensoring the
nine elementary matrix-unit systems gives a unital copy of
`M_2(C)^(tensor 9)=M_(2^9)(C)`.  A finite-dimensional module over this
matrix algebra is a direct sum of its defining module: choose one minimal
matrix-unit range and transport it by the matrix units.  This gives exactly
the tensor decomposition `(NHR5)` and is also a direct proof of the claimed
multiplicity uniqueness.

The statement passes directly to a norm matrix corona.  The displayed
relations are exact in the quotient.  For arbitrary matrix lifts, the
finitely many Fourier polynomials in `(NHR3)` are asymptotic projections,
and their conjugacy errors tend to zero in operator norm.  Spectral cutting
at `1/2` changes them by operator norm tending to zero.  Two projections at
distance less than one have equal rank, so all `2^9` rounded atom ranks are
eventually equal up to the vanishing rounding remainder.  Thus each has
asymptotic normalized rank `2^(-9)` of the active marked core, without a
canonical character assumption or a finite-group stability input.

Every root factor in the fixed center-chain and native-Whitehead words has
both indices in `(NHR6)`.  For `10<=k<=18`, neither index-composition
condition with `(1,k)` or `(k,3)` can occur.  The Steinberg commutator rule
therefore makes every such factor commute with `C_k,D_k`; products do too.
The commutant of `M_(2^9)(C) tensor 1` is
`1 tensor B(M)`, proving `(NHR7)`.  Normalized traces of star-polynomials
in the selector operators are unchanged by tensoring with the normalized
trace on `M_(2^9)(C)`.  This proves the spectator fence.

For the coefficient packet, equal-length prefix cancellation is

```text
t_alpha s_beta=delta_(alpha,beta).
```

Therefore

```text
(s_1t_alpha)(s_beta t_1)=delta_(alpha,beta)s_1t_1,
```

and the root commutator rule proves `(NHR9)`.  Distinct `X_alpha` are
independent: multiplying a putative coefficient relation
`sum lambda_alpha s_1t_alpha=0` on the left by `t_1` and on the right by
`s_beta` extracts `lambda_beta`.  Hence the stated ten-bit subgroup is
elementary abelian, and conjugation by the `Y_beta` gives the same
coordinate-flip proof of uniformity.

The adjacent Whitehead roots have both indices in `{7,8,9}`, disjoint from
`{1,2,3}`, so they centralize `X_alpha,Y_beta,z`.  A center-chain terminal
arm `x_(k,2)(b)` is composable with
`Y_beta=x_23(s_beta t_1)`.  The Steinberg formula gives `(NHR10)`.
When its coefficient is nonzero this is a root outside the displayed
extraspecial packet, so the packet is not normalized and the unitary
equating two global character atoms can move the Hecke carrier.  Trace
invariance then gives no equality of their conditional masses.  If the
prefixes are instead chosen in the common annihilator of the finitely many
terminal-arm coefficients, the commutators vanish and the full packet
commutes with the Hecke carrier.  The matrix-factor argument `(NHR7)` then
applies and shows that it is a spectator.  This proves the second placement
fence and completes the claim.
