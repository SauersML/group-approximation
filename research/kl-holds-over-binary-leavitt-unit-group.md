---
rg: 2
id: kl-holds-over-binary-leavitt-unit-group
kind: claim
title: Every nonsingular one-variable equation over the binary Leavitt unit group injects its coefficients
root: true
refuted_by: [kl-violating-equation-over-leavitt-unit-group]
distinct_from:
  kl-violating-equation-over-leavitt-unit-group: that asks for one violating equation and would refute this; this is the positive statement over the same group, and exactly one of the two can end up established.
  kervaire-laudenbach-nonsingular-conjecture: that quantifies over all coefficient groups; this is the single coefficient group R^x, where the conjecture is not known and where a failure would also give an explicit nonhyperlinear group.
  kervaire-laudenbach-holds-for-hyperlinear: that is the theorem for hyperlinear coefficients; R^x is not known to be hyperlinear, so that theorem does not apply here.
---

For `R^x = L_(F_2)(1,2)^x`, every `w in R^x * <t>` with `deg_t(w) != 0`
gives an injective coefficient map `R^x -> (R^x * <t>)/<<w>>`.

This is the negation of `kl-violating-equation-over-leavitt-unit-group`, and
the two claims record each other as refuters.  It is marked `root` because it
heads the positive side of the Leavitt Kervaire--Laudenbach decision, which
nothing else in the graph consumes: a proof here proves no universal statement
and no approximation property of `R^x`.

Because `R^x` is simple (`binary-leavitt-unit-group-is-simple`), the radical
bound of `nonsingular-adjunction-preserves-approximation-radicals` gives a
clean dichotomy for the kernel of the coefficient map: it lies in
`Rad_hyp(R^x)`, which is `1` or all of `R^x`.  If `R^x` is hyperlinear, this
claim holds.  If `R^x` is not hyperlinear, the radical bound says nothing.

## Attempts

1. **Hyperlinearity.**  Conditional route
   `kl-leavitt-holds-on-the-unstable-steinberg-branch`: on the unstable branch
   of the Steinberg HS fork, `EL_4(L) = R^x` is hyperlinear, and the
   Gerstenhaber--Rothaus--Pestov theorem applies.  Open with that branch.
2. **Operator-MF roots.**  Dead.  `kervaire-laudenbach-holds-for-mf` needs a
   faithful norm-corona model, and `mf-root-transport-is-vacuous-on-leavitt-units`
   records that `R^x` has no nontrivial one.  Recorded as
   `kl-leavitt-holds-via-mf-root-transport`.
3. **Short equations.**  Proved for variable length at most five by
   `length-five-kl-fence-for-leavitt-equations` (Evangelidou's universal
   length-five theorem), and for coefficient packets whose entries generate a
   residually finite-dimensional subalgebra of `L` by
   `leavitt-rfd-entry-packets-satisfy-kl`.  Neither is a route to this claim:
   both leave full-support words of length at least six.
4. **Rank-metric roots over the algebraic closure of `F_2`.**  Deferred.  If
   `R^x` embedded in a rank-metric ultraproduct of `GL_d(Fbar_2)`, an
   algebraic replacement for the degree argument would give roots.  Neither
   ingredient is available.  The replacement cannot be the naive fixed-size
   statement: `T^2 = I + E_12` has no solution in `GL_2(Fbar_2)`, since the
   square of a unipotent `2 x 2` matrix in characteristic two is the identity.
   It does have one after amplifying to `GL_4`.
5. **Thompson's V is a necessary sub-case.**  `thompson-v-kl-from-leavitt-kl`
   derives `kl-holds-over-thompson-v` from this claim, and
   `leavitt-kl-violation-from-thompson-v-violation` turns every violation over
   `V` into a violation here.  So a positive proof must in particular solve
   every nonsingular equation over `V`, a finitely presented infinite simple
   group with torsion where no known positive theorem applies either.
6. **Homology and Schur multipliers.**  Dead as certificates.  `R^x` is
   integrally acyclic (`leavitt-steinberg-map-iso-from-rank-three`, (KH1) at
   `r = 1`).
   - The relative complex `X_w = K(R^x,1) v S^1 u_w e^2` has `H_1 = Z/|m|`
     and `H_k = 0` for `k >= 2`, for every `w` of degree `m`.  A violation
     forces `pi_1(X_w) = C_|m|` (`kl-simple-failure-leaves-only-the-cyclic-quotient`,
     `binary-leavitt-unit-group-is-simple`), and then `pi_2(X_w) = Z^(|m|-1)`;
     at `m = +-1` the complex is contractible.  Neither outcome contradicts
     anything homological.
   - Over `R^x` itself Schur injectivity is vacuous, since `H_2(R^x) = 0`.
   - The recorded cycle with `universal-schur-injectivity-for-nonsingular-adjunctions`
     enters only through `kl-failure-yields-a-schur-kill`, the direction used
     here.  For `Q_a = R^x *_(<a>) (<a> x Z)`, Mayer--Vietoris with
     `H_2(<a>) = H_2(R^x) = 0` gives `H_2(Q_a) = H_1(<a>)`, the torus class
     and nothing else.  The same sequence over `R^x_w` shows that the torus
     class survives exactly when `<a> -> R^x_w` is injective.  So Schur
     injectivity over the family `{Q_a}` is a restatement of this claim, not
     a reduction.
