---
rg: 2
id: sl3-lattice-exact-packets-have-linear-repair
kind: claim
title: Exact SL3 lattice packets admit linear same-dimensional repair to full arithmetic congruence representations at every prime
distinct_from:
  odd-congruence-lambda-exact-sector-collapses: That is qualitative commutant collapse with an already coprime exact lattice restriction; this repairs arbitrary primary and mixed levels to actual full arithmetic representations with a linear matrix estimate.
  coprime-sector-collapse-is-robust-to-small-p-admixture: That consumes vanishing primary mass for a qualitative HNN commutant conclusion; this gives explicit bounds for repairing the entire actor in the same dimension and needs only a finite overlap packet and one Weyl relation.
  unbalanced-torus-extracts-near-central-denominator-coordinate: That starts from an exact full arithmetic reference representation and bounds one auxiliary projective energy; this constructs the full arithmetic reference from a possibly primary exact lattice representation and bounds ordinary generator distance.
artifacts:
  - research/artifacts/sl3-linear-lattice-to-actor-repair-2026-09-08.md
---

Fix any prime `p`, including `p=2`. Set

    C=SL_3(Z),       A=SL_3(Z[1/p]),
    h=diag(p,1,p^-1),       D=C cap h^-1 C h.

Fix a finite Kazhdan generating set `S_D` for `D`, with constant
`kappa_D` in the distance-to-fixed-vectors convention. Let `w_12,w_23`
be determinant-one signed permutation matrices implementing the indicated
coordinate transpositions. Let `C_p` be the constant in
`sl3-primary-mass-has-a-uniform-quadratic-gap`, for these overlap data.

For any genuine congruence representation `sigma:C->U(d)` and unitary
`H in U(d)`, define normalized-HS defects

    epsilon_D=max_(s in S_D)
       ||H sigma(s)-sigma(h s h^-1)H||_2,
    epsilon_W=||H( sigma(w_23)H sigma(w_23)* )*
                  -sigma(w_12)H sigma(w_12)*||_2.

There is an exact representation `rho:A->U(d)`, factoring through a
congruence quotient of level coprime to `p`, such that

    sup_(c in C)||sigma(c)-rho(c)||_2
      <=2 sqrt(C_p) epsilon_D,                            (LAR1)

    ||H-rho(h)||_2
      <=epsilon_W
         +[8 sqrt(C_p)+(4/kappa_D)(1+4 sqrt(C_p))]
             epsilon_D.                                 (LAR2)

The dimension is unchanged. The constants are independent of dimension,
conductor depth, multiplicities, and trace profile. No invariance of a
retained corner under `H` is required. The primary-gap constant is
existential, so these are linear bounds without an asserted effective
numerical constant.

Consequently, every asymptotic arithmetic actor whose lattice restriction
is pointwise close in the same dimension to exact congruence
representations is pointwise close to exact full arithmetic congruence
representations. Every lattice-exact matrix-ultraproduct actor therefore
lies in the already established coprime sector after changing
representatives. Its lattice and actor commutants coincide, and it cannot
support a scalar relative matrix witness.

This is a relative repair theorem with an exact lattice input. It does not
correct an arbitrary approximate lattice tuple or establish the full
nonhyperlinearity target.
