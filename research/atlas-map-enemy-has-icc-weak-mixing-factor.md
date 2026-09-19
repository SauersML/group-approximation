---
rg: 2
id: atlas-map-enemy-has-icc-weak-mixing-factor
kind: claim
title: The Atlas MAP enemy reduces to an ICC CE factor with vanishing finite-chart returns
distinct_from:
  atlas-hyperlinear-enemy-is-map-or-large-simple: that isolates a minimally almost periodic quotient after finite-dimensional shadows are removed; this replaces that quotient by a centerless ICC one and computes its adjoint mixing on the two chart algebras.
  atlas-six-relator-hyperlinear-escape-test: that characterizes the enemy by a nontrivial hyperlinear quotient and regular chart trace; this proves the enemy may be required to have a diffuse factorial canonical trace and weakly mixing conjugation representation.
  atlas-radius-nine-packet-gram-sos-is-tracial: that fences universal packet-Gram positivity because of the Leavitt tracial countermodel; this gives a quotient-specific obstruction to every fixed finite-chart return or compact adjoint sector.
  finitely-generated-map-lef-has-perfect-regular-chart-microstates: that shows finite chart synchronization alone is compatible with MAP hyperlinearity; this derives the stronger ICC and weak-mixing form forced by the concrete Atlas quotient and therefore identifies what still must be coupled by its fixed relators.
  character-diracization-limit: that turns an arbitrary character into the regular character of its scalar-kernel quotient; this uses central-quotient descent directly and preserves the two injected A8 charts and their fixed normal generator.
---

**ESTABLISHED CONDITIONAL REDUCTION.**  Suppose the minimally almost periodic
branch of the six-relator Atlas enemy exists: there is a nontrivial
hyperlinear quotient

```text
Gamma_6 -> Lambda
```

and every finite-dimensional unitary representation of `Lambda` is trivial.
Then there is another nontrivial quotient

```text
Gamma_6 -> Lambda_bar
```

with all of the following properties.

1. `Lambda_bar` is hyperlinear, minimally almost periodic, centerless and
   ICC.  Consequently

   ```text
   M=L(Lambda_bar)
   ```

   is a diffuse Connes-embeddable II1 factor.
2. Both marked `A8` charts inject into `Lambda_bar`.  Every nonidentity chart
   element, in particular one fixed standard transvection `t`, normally
   generates `Lambda_bar`.
3. The conjugation representation

   ```text
   Ad lambda : Lambda_bar -> U(L2(M) minus C1)
   ```

   is weakly mixing: it has no nonzero finite-dimensional invariant
   subspace.  The single orbit

   ```text
   {lambda(g t g^-1):g in Lambda_bar}
   ```

   generates `M` as a von Neumann algebra.
4. Let

   ```text
   V_i=L2(L(A8_i)) minus C1,       i=1,2.
   ```

   There is a sequence `g_n in Lambda_bar` such that

   ```text
   max_(i,j in {1,2})
     ||P_(V_i) Ad(lambda(g_n))|_(V_j)|| -> 0.          (AMW1)
   ```

   Equivalently, conjugates of both centered finite chart algebras can be
   moved simultaneously to have arbitrarily small conditional-expectation
   return to either chart.

Therefore the surviving diffuse enemy cannot contain a finite-dimensional
adjoint memory sector carrying the fixed chart packet, nor can a fixed Hecke
or conditional-expectation argument force a uniform positive return between
the two finite chart spaces.  A contradiction must use the six literal
Atlas relators to prevent the weak-mixing moves `(AMW1)`; finite subgroup
regularity, character tensor powers, and packet expectations alone do not.

This does not exclude the enemy.  It replaces an arbitrary diffuse MAP
quotient by one canonical CE group factor with a single weakly-mixing,
normally-generating conjugacy orbit.
