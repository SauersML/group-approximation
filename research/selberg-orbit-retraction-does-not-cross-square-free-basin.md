---
rg: 2
id: selberg-orbit-retraction-does-not-cross-square-free-basin
kind: claim
title: Selberg orbit retraction starts after, not before, square-free basin authentication
distinct_from:
  regular-congruence-endpoint-orbit-has-uniform-selberg-retraction: that proves the uniform estimate under exact regular congruence character input; this proves that the raw five-word endpoint tuple does not provide that input.
  modular-vertex-extension-does-not-force-congruence: that gives the abstract representation-theoretic failure of congruence from vertex extension; this identifies its exact place in the square-free orbit-distance argument.
  bs14-hs-stability-does-not-supply-relative-op-basin: that rules out an operator-norm basin from BS stability; this is a logical and exact bending firewall against applying congruence conditional expectation to an unauthenticated endpoint.
---

The uniform estimate in
`regular-congruence-endpoint-orbit-has-uniform-selberg-retraction` cannot be
applied directly to a square-free tuple with small defects

```text
X^2, (XR)^2, (XT)^3, RTR^(-1)T^(-4), (XT^2R)^3.       (SBF1)
```

After `iwahori-two-triangle-torsion-normal-form`, the torsion rows give
honest modular `C_2*C_3` vertex data, but they do not make the `X`-generated
vertex factor through any congruence quotient.  Selberg averaging of

```text
beta(b)A=rho(b)A eta(b)^*
```

has a level-independent gap only when **both** factors are already in the
odd-congruence sector.  If `eta` is an arbitrary finite-dimensional modular
representation, `beta` need not factor through a congruence quotient at all.
Invoking the Selberg constant at this point is therefore exactly the
missing basin assertion in disguise.

Nor can one estimate the authenticated edge mismatch relative to a fixed
canonical endpoint by the five defects.  The exact family in
`congruence-iwahori-endpoint-fiber-contains-core-commutant-orbits` has all
five defects equal to zero while its relative gauge from the canonical
regular endpoint obeys

```text
||[XX_0^(-1),T]||_2>=sqrt(2).                          (SBF2)
```

Thus even exact relations permit a macroscopic change of endpoint
representative.  One must first quotient by the core-commutant orbit and
authenticate the resulting modular representation type; only then does
Selberg give the uniform retraction.

Consequently level dependence is fully separated:

1. **inside the authenticated regular congruence sector:** the orbit
   retraction constant is `4/kappa`, uniform in `p^k` and multiplicity;
2. **from raw square-free defects to that sector:** no Selberg estimate is
   available.  This is precisely
   `regular-iwahori-relative-congruence-exactification`, not a deteriorating
   finite-level constant that property `(tau)` can repair.
