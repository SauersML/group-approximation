---
rg: 2
id: sl3-odd-correctable-sector-has-uniform-projective-modulus
kind: claim
title: The odd-correctable SL3 sector has a uniform projective transfer modulus
artifacts:
  - research/artifacts/sl3-odd-correctable-projective-modulus-2026-08-22.md
distinct_from:
  odd-congruence-lambda-exact-sector-collapses: that is an ultraproduct relative-commutant equality for exactly central witnesses; this extracts its uniform finite-dimensional consequence for projectively central auxiliary unitaries and permits asymptotically near-exact lattice restrictions.
  sl3-near-exact-leaks-live-in-the-two-primary-tower: that treats the fixed quasi-regular leak configuration; this treats every auxiliary unitary and every projective trace-square far-sector witness.
  odd-congruence-native-sector-has-defect-only-gap: that gives a linear inequality for one native trace-zero lamp packet; this gives a nonconstructive uniform modulus for arbitrary projective witnesses.
---

Put

```text
Gamma=SL_3(Z[1/p]),       Lambda=SL_3(Z),
h=diag(p,1,p^(-1)).
```

Fix presentations and generator words.  Consider assignments
`rho_j` with ambient relator defect `delta_j->0`, and unitaries `U_j`, such
that

```text
q_j=sum_(c in S_Lambda)
      (1-|tr([U_j,rho_j(c)])|^2) ->0.                 (OCP1)
```

Assume the restrictions `rho_j|_Lambda` are within `xi_j->0` on generators
of exact representations `sigma_j` factoring through congruence levels
`N_j` coprime to `p`.  Then

```text
1-|tr([U_j,rho_j(h)])|^2 ->0.                         (OCP2)
```

No canonical-character hypothesis and no multiplicity restriction are
needed.

Equivalently, there is a dimension-, level-, and multiplicity-independent
modulus `eta_odd(t)->0` such that throughout this sector

```text
e(U,rho(h))
 <= eta_odd(delta+xi+sum_(c in S_Lambda)e(U,rho(c))). (OCP3)
```

The modulus is asserted existentially; no linear rate is claimed.

Proof mechanism.  If `(OCP2)` failed, pass to a tracial matrix ultraproduct.
The ambient assignments give an exact representation `pi` of `Gamma`, and
the near-exact restrictions give a Lambda-exact congruence lift of level
prime to `p`.  Equation `(OCP1)` says the ultraproduct unitary `U` commutes
with `pi(Lambda)` projectively.  The scalar commutators form a character of
`Lambda`; perfectness of `SL_3(Z)` makes it trivial.  Hence

```text
U in pi(Lambda)'.
```

Now `odd-congruence-lambda-exact-sector-collapses` gives
`pi(Lambda)'=pi(Gamma)'`, so `U` commutes with `pi(h)`, contradicting the
fixed projective energy in `(OCP2)`.  The same sequential contradiction
proves the uniform modulus `(OCP3)`.

Consequently a fixed-gap countermodel to
`projective-commutant-transfer-for-arithmetic-pair` for the `SL_3` pair must
have one of exactly two features:

1. a lattice restriction uniformly far from every exact finite-dimensional
   representation; or
2. every available exactification uses congruence levels divisible by `p`
   (possibly mixed levels).

For `p=2` this is precisely the branch in which a two-primary component is
present, already isolated by the mixed-level analysis.  Purely odd
congruence levels and all their multiplicity data cannot support a
projective far-sector escape.  This lemma alone does not give a lower bound
on the two-primary mass inside a mixed-level representation.
