---
title: STW LXVI higher-rank audit --- triangular dyadic bundle systems are K-theoretically feasible (2026-08-30)
---

## Correction to the epsilon-tower proposal

A literal infinite family of nonzero finite-rank bundles satisfying
`eta_m ~= 2 eta_(m+1)` cannot exist: ranks would obey
`rank(eta_1)=2^k rank(eta_(k+1))` for every `k`.  The correct inductive
object is triangular.  Stage `K` contains only levels `m=0,...,K`; the
new deepest level has rank one, and the connecting map doubles every old
level while carrying it into the next triangle.

## Explicit integral construction

Take `N_K=2^K`, `X_K=(S^2)^(N_K)`, and
`L_K=tensor_(i=1)^(N_K) H_i`, where `H_i` is the coordinate Hopf line.
Set

`eta_(K,m)=2^(K-m)L_K`.

Then `eta_(K,m)=2 eta_(K,m+1)`.  If `r=2^(K-m)`,

`e(eta_(K,m))=(sum_i x_i)^r
 = r! sum_(|F|=r) product_(i in F)x_i !=0`,

because `r<=N_K` and
`H^*(X_K;Z)=Z[x_1,...,x_(N_K)]/(x_i^2)` is torsion-free.

Let `pi_K:X_(K+1)->X_K` be projection and let `D_K` be the tensor product
of the Hopf lines on the new coordinates.  The positive bundle map

`Phi_K(xi)=2(D_K tensor pi_K^*xi)`

sends `eta_(K,m)` exactly to `eta_(K+1,m)`.  It is implemented by a
two-branch diagonal star homomorphism between the stable homogeneous
algebras.  On `K^0` it is pullback, followed by multiplication by the
invertible line class `[D_K]`, followed by multiplication by two.

## Direct-limit calculation

The diagonal class `L_m` defines a nonzero positive limit class `q_m`.
At every common later stage, `q_m=2q_(m+1)`.  The rank quotient is the
direct system `Z --2--> Z --2--> ...`, hence `Z[1/2]`, with `q_m`
corresponding to `2^(-m)` after a choice of initial normalization.

So neither rank, integral Euler classes, nor ordered K-theory blocks the
finite-depth root programme.  This does **not** revive the refuted V4
construction: using these same two identical branches as the global
finiteness mechanism encounters the established Hall and
proper-infiniteness obstructions.  A successful LXVI construction would
need the triangular classes embedded in connecting maps whose remaining
branches supply simplicity while a new, non-multiplicity finiteness
certificate survives.

## Analytic postscript

The most direct non-uniform version is now also ruled out by
`one-cofinal-rank-amplifying-branch-forces-proper-infiniteness`.  It is not
enough to double only one distinguished triangular summand while leaving
the other branches unpaired.  The infinitely many bounded-support
simplicity branches can all be followed through that same distinguished
continuation; their rank demand eventually exceeds their private
coordinate capacity.  The exact finite obstruction is the weighted Hall
criterion in `hopf-power-blocks-obey-weighted-hall-euler-criterion`, and
the dimension argument upgrades its failure to proper infiniteness.
