---
rg: 2
id: regular-iwahori-exactification-is-regular-branch-liftability
kind: claim
title: Regular Iwahori exactification is exactly regular-branch HS liftability
distinct_from:
  regular-iwahori-relative-congruence-exactification: that states the arithmetic exactification target for exact modular vertices; this proves that, after the established vertex and congruence repair theorems, the target is equivalent to correcting every regular microstate of the whole group.
  regular-branch-liftability-plus-fd-kernel-forces-nonhyperlinear: that turns regular-branch liftability plus a finite-dimensional residual kernel into nonhyperlinearity; this identifies regular Iwahori exactification itself with the liftability hypothesis for the arithmetic endpoint.
  relative-first-triangle-rounding-has-an-odd-root-branch-firewall: that gives an explicit failure of independently lifting the square-root branch after one triangle is rounded; this is the global equivalence showing why qualitative ultraproduct lifting cannot bypass relative exactification.
---

Put

```text
Gamma=SL_2(Z[1/2])=C_+ *_(B_+=B_-) C_-,
C_+=C_-=SL_2(Z),
```

with the Iwahori identification used in
`iwahori-local-global-defect-question`.  The following two properties are
equivalent.

1. **Regular relative congruence exactification.**  Every sequence of exact
   vertex representations `pi_(n,+),pi_(n,-):C_+*C_->U(d_n)` whose edge
   defect tends to zero and whose induced ultraproduct representation of
   `Gamma` has the regular character is `o(1)`-close to a pair of exact odd
   congruence vertex representations with edge defect tending to zero.

2. **Same-dimensional regular-branch liftability.**  Every normalized-HS
   microstate sequence of `Gamma` with limiting character `delta_e` is
   `o(1)`-close on a fixed generating set to genuine representations

   ```text
   rho_n:Gamma->U(d_n).
   ```

The equivalence uses three established inputs: same-dimensional HS stability
of each modular vertex, uniform repair of arbitrary odd-congruence Iwahori
pairs, and the classification of every finite-dimensional representation of
`Gamma` as an odd-congruence representation.

Therefore the qualitative ultraproduct version of basin capture is not a
weaker substitute for the missing quantitative theorem.  Exactifying the
two `PSL_2(Z)`/`SL_2(Z)` triangles merely puts an arbitrary regular
microstate into the normal form in item 1.  Proving that the resulting exact
ultraproduct homomorphism has nearby coordinatewise exact congruence lifts is
already the entire regular-branch stability problem.

In particular, exact endpoint classification and character rigidity do not
provide a lifting principle.  They say respectively what a coordinatewise
lift would look like and that the surviving ultraproduct character is
regular; item 2 asks for the existence of those lifts.  The explicit
odd-root branch firewall shows why exactness in the quotient alone cannot
be used to manufacture them after an independent first-triangle rounding.

