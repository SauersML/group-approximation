---
rg: 2
id: arith-clifford-covariance-preserves-projective-energy
kind: claim
title: Arithmetic--Clifford normalizer covariance preserves every projective transfer enemy
distinct_from:
  spherical-quadrature-tensors-through-clifford-folner-windows: that uses commuting tensor factors and only finite spherical moments; this permits genuinely noncommuting arithmetic transport of the Clifford packet and preserves the full arithmetic assignment and its relative-commutator energies.
  projective-label-pullbacks-have-conjugate-stationary-absorbers: that proves an abstract presentation with projective occurrence labels has a stationary representation; this records the extra invariant needed by the arithmetic route, namely exact preservation of every projective trace-square commutator and of canonical-character microstates.
  central-hecke-controlled-multipaths-remain-sectorwise: that concerns additive sums controlled by central Hecke atoms; this treats one-path normalizer covariance and identifies additive same-corner interference as the first operation outside the theorem.
---

# Arithmetic--Clifford normalizer covariance preserves every projective transfer enemy

ESTABLISHED.  Let

```text
Gamma=<S | R>
```

be a finitely presented arithmetic group, let `K` be a finite packet group
represented on `V`, and suppose a homomorphism

```text
ell:Gamma -> Lambda
```

labels an action `alpha:Lambda->Aut(K)`.  Assume the action is implemented on
`V` by a finite-dimensional projective normalizer system

```text
C_l pi(k) C_l^*=pi(alpha_l(k)),
C_l C_m=c(l,m)C_(lm).                                    (ACN1)
```

Adjoin the genuinely mixed covariance relations

```text
s k s^-1=alpha_(ell(s))(k)       (s in S, k in K).        (ACN2)
```

These relations need not be commutation relations; a nontrivial `alpha`
makes them alternate essentially between the arithmetic and Clifford
generators.  Nevertheless they cannot improve any projective
relative-commutator transfer inequality.

Indeed put

```text
T_l=C_l tensor conjugate(C_l).                            (ACN3)
```

Then `T` is an honest representation of `Lambda`.  Given any (possibly
approximate) matrix assignment `rho:S->U(H)` and any unitary `U in U(H)`, set

```text
rho_hat(s)=rho(s) tensor T_(ell(s)),
pi_hat(k)=I_H tensor pi(k) tensor I_(conjugate V),
U_hat=U tensor I_(V tensor conjugate V).                  (ACN4)
```

Every covariance relation `(ACN2)` is exact.  For every arithmetic relator
`r in R`,

```text
rho_hat(r)=rho(r) tensor I,
||rho_hat(r)-I||_2=||rho(r)-I||_2.                        (ACN5)
```

More strongly, for every arithmetic word `g`,

```text
[U_hat,rho_hat(g)]=[U,rho(g)] tensor I,                   (ACN6)
```

and hence

```text
1-|tr([U_hat,rho_hat(g)])|^2
 =1-|tr([U,rho(g)])|^2.                                  (ACN7)
```

Thus subgroup energy, target energy, and arithmetic presentation defect in
`projective-trace-square-transfer-for-sl3-pair` are all preserved exactly.
This is a skew tensor escape: the arithmetic matrices do act nontrivially on
the Clifford factor, but the dangerous arithmetic multiplicity remains
completely independent.

The same construction preserves canonical-character enemies.  For a word
`w` in the arithmetic generators and an HNN/block-swap letter represented by
`U`, evaluation factors as

```text
w(rho_hat,U_hat)=w(rho,U) tensor T_(ell(bar w)),           (ACN8)
```

where `bar w` is the arithmetic projection of `w`.  Therefore
`tr(w(rho,U))->0` implies `tr(w(rho_hat,U_hat))->0`.  Adding the covariance
packet cannot remove a canonical regular HNN or adjacent-double enemy.

There is a finite-groupoid version with the same proof: replace `(ACN3)` by
the honest bisection representation on
`direct_sum_a V_a tensor conjugate(V_a)` supplied by conjugate doubling.
Consequently the actual finite depth-two Clifford sector changes do not alter
the conclusion.

The first incidence outside this theorem is not a longer alternating word.
Every one-path normalizer word still factors as `(ACN8)`.  One needs an
additive same-corner entry containing at least two coherent packet paths, or
an identification of an arithmetic coefficient with a non-normalizer packet
corner.  Only such a relation prevents arrowwise conjugate absorption and can
make the arithmetic multiplicity participate in the Clifford test.
