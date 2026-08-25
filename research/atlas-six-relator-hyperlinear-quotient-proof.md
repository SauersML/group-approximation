---
rg: 2
id: atlas-six-relator-hyperlinear-quotient-proof
kind: route
title: Pass between exact regular ultraproduct charts and a bridge-retaining hyperlinear image
target: atlas-six-relator-hyperlinear-escape-test
requires:
  - atlas-19243-centrality-forces-s3-distance
  - regular-atlas-linearized-h-coercivity
  - atlas-charts-overlap-trivially
  - atlas-six-relator-nontrivial-quotients-inject-charts
---

The equivalence between items 2 and 3 first uses
`atlas-six-relator-nontrivial-quotients-inject-charts`: every nontrivial
quotient injects both factors.  If all four bridges vanished in a hyperlinear
quotient, its canonical regular microstates would put the relative frame in
the `H` commutant, contradicting the exact `19243` floor below.  Hence a
fixed bridge survives.

Suppose now that an exact common-orbit model is given.  Write it as

```text
Phi:Gamma_6 -> U(M_omega),
M_omega=product_omega (M_(20160 k_n),tr),              (HUQP1)
```

after the standard finite-group exactification and regularization of the two
marked `A8` restrictions.  Let

```text
Lambda=Phi(Gamma_6).
```

As a subgroup of the unitary group of a tracial matrix ultraproduct,
`Lambda` is hyperlinear, and `Phi` factors through the quotient map
`q:Gamma_6 -> Lambda`.  A nonidentity element of either marked `A8` has
normalized distance `sqrt(2)` from the identity in its regular restriction.
Therefore `q` is injective on both finite factors.

Assume all four fixed bridge words vanish.  In common-frame coordinates this
says that the relative chart unitary `U` commutes with the four
`rho(t_ell)`, hence with `rho(H)`.  The exact calculation
`atlas-19243-centrality-forces-s3-distance` then gives

```text
||pi_U(c_19243)-1||_2=sqrt(2),                         (HUQP2)
```

contrary to the defining relation of `Gamma_6`.  Thus some fixed word
`b_ell` survives in `Lambda`.  Moreover its covariance norm is positive, and
the dimension-free operator inequality

```text
sum_(ell=1)^4 ||rho(t_ell)U rho(t_ell)^*-U||_2^2
 <= C_lin sum_(j in {0,11,30,44,55}) ||rho(z_j)U||_2^2 (HUQP3)
```

shows that the five-row additive energy is positive.

Conversely, let `q:Gamma_6 -> Lambda` be a hyperlinear quotient which injects
both marked factors and retains `b_ell`.  Use **canonical-trace
microstates** of the hyperlinear group `Lambda`: equivalently, take a
trace-preserving embedding

```text
L(Lambda) -> product_omega (M_(d_n),tr).               (HUQP4)
```

This canonical-trace choice is essential.  Since each `q(A8_i)` is an
embedded finite subgroup, its restriction in `(HUQP4)` has the regular
character, not merely an arbitrary finite-group character.  Finite-group
normalized-HS stability changes the coordinate restrictions by `o(1)` to
exact representations.  Character orthogonality makes their irreducible
multiplicities asymptotically Plancherel.  Taking `|A8|` copies, extracting
the common regular core and changing the `o(d_n)` complement gives, exactly
as in `leavitt-regular-atlas-hyperlinearity-criterion-proof`, coordinate
models of the form

```text
pi_n(a)=lambda(a) tensor I_(k_n)                       (a in A8_1),
pi_n(a)=U_n(lambda(a) tensor I_(k_n))U_n^*             (a in A8_2). (HUQP5)
```

All fixed six-relator defects still tend to zero, so `(HUQP5)` defines an
exact common-orbit model in the ultraproduct.  The fixed surviving group word
has canonical norm

```text
||lambda_Lambda(q(b_ell))-1||_2=sqrt(2).               (HUQP6)
```

In the coordinates `(HUQP5)`, this is precisely the `t_ell` covariance norm.
Applying `(HUQP3)` yields five-row additive energy at least `2/C_lin`, hence
strictly positive.  This proves the reverse implication and also shows that
no unrecorded choice of character is being used.

For completeness, evaluate the intrinsic element `(HUQ4)`.  In the common
frame `(HUQP5)`,

```text
pi_n(i_1(g)i_2(g)^(-1))
 =lambda(g)U_n lambda(g)^*U_n^*.
```

Summing with the coefficients of `z_j` gives

```text
pi_n(Z_j)=(rho(z_j)U_n)U_n^*.
```

Normalized Hilbert--Schmidt norm is invariant under the final right unitary,
so `tau(pi(h_5))=A(U)` in the ultraproduct.  A CE trace in the regular locus
produces the hyperlinear GNS image used above; conversely the canonical trace
of any hyperlinear quotient injecting the factors pulls back to such a CE
trace.  This proves the trace-locus formulation `(HUQ6)`.  The canonical
Leavitt trace supplies the asserted non-CE point by
`atlas-six-relator-leavitt-tracial-countermodel`.

Finally, `Gamma_6` maps onto the binary Leavitt group `Q`.  Both `A8` factors
embed in `Q`, and `atlas-charts-overlap-trivially` makes, for example, the
fixed word `i_2(t_1)i_1(t_1)^(-1)` nontrivial in `Q`; it is therefore already
nontrivial in `Gamma_6`.  If `Gamma_6` were hyperlinear, take its identity
quotient in the equivalence above.  The resulting positive-energy exact
ultraproduct model contradicts `atlas-five-row-operator-phase-lift`, proving
`(HUQ3)`.
