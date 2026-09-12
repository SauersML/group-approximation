---
rg: 2
id: zpc-orbitwise-menu-class-needs-constant-menu-component-proof
kind: route
title: Freeze the menu on an unreadable-invariant set and read off the ergodic component
target: zpc-orbitwise-menu-class-needs-constant-menu-component
requires: []
---

**(1) Equivalence.**  For each menu value `c in Menus` put

```text
A_c = { y in Y : m(g.y) = c for every g in U } = intersection_(g in U) g^(-1) m^(-1)(c).
```

`U` is countable, so `A_c` is measurable, and it is `U`-invariant: if
`y in A_c` and `h in U`, then `m(g.(h.y)) = m((gh).y) = c` for all `g`, since
`gh in U`.  Also `A_c` is contained in `m^(-1)(c)`.

The orbitwise resource `(ZOM2)` is, verbatim, a positive-measure measurable
set `B` inside one readable atom on whose whole `U`-orbit the selected menu
is the base menu `c`; that is exactly `mu(B)>0` with `B ⊆ A_c` up to null
sets.  So the resource exists iff `mu(A_c)>0` for some `c`.

Take the ergodic decomposition `mu = integral mu_omega d omega` for
`U ↷ (Y,mu)`.  Each `A_c` is `U`-invariant, so `mu_omega(A_c) in {0,1}` for
a.e. `omega`, and

```text
mu(A_c) = integral mu_omega(A_c) d omega.
```

Thus `mu(A_c)>0` iff a positive-measure set of components has
`mu_omega(A_c)=1`.  Now `mu_omega(A_c)=1` iff `m` is a.e. equal to `c` on the
component `omega`:
- if `m equiv c` a.e. on `omega`, then `m^(-1)(c)` is `mu_omega`-conull;
  each `g^(-1) m^(-1)(c)` is conull (`U` preserves `mu_omega`); a countable
  intersection of conull sets is conull, so `mu_omega(A_c)=1`;
- conversely `A_c ⊆ m^(-1)(c)`, so `mu_omega(A_c)=1` forces `m equiv c`
  a.e. on `omega`.

Hence the orbitwise resource exists iff some positive-measure component has
an essentially constant selected menu.  This is claim (1).

**(2) Collapse.**  Fix such a component `Y_c` with `m equiv c` a.e.  Almost
every point selects the one menu `c`, so after substituting the readable
signs that define `c`, every controlled-linear constraint active anywhere in
the game reduces on `Y_c` to a row of the single finite affine system `E_c`,
and the same-question and edge ZPC commutators hold globally
(`zpc-readable-variables-global-boolean-field` and edge commutation).  In the
negative central sector `J=-1`.  The unreadable involutions therefore give a
perfect commuting-operator model, with `J=-1`, of the ordinary binary LCS
`L(G,c)=L(S_L,E_c,C)` whose rows are `E_c` together with the commutation
ancillas.

Suppose `L(G,c)` had a perfect finite-dimensional (matrix) strategy.
Combining its operator solution on the unreadable variables with the
deterministic readable answers realizing the menu `c` yields a
finite-dimensional tailored strategy satisfying every selected constraint,
hence perfect for `G`; this contradicts `omega*(G)<1`.  So `L(G,c)` has a
perfect commuting-operator strategy and no finite-dimensional one, and by
`finite-linear-commutation-system-to-lcs` its solution group is a finitely
presented nonhyperlinear group.  No other requirement of
`zpc-freezing-from-orbitwise-equation-menu` is used.

**(3) Consequence.**  (1) and (2) give a decision procedure with no slack:
the orbitwise resource is available exactly when a component is already an
LCS gap, i.e. already an endpoint.  The remaining, genuinely open regime is a
`U`-ergodic witness whose menu map takes at least two values (a nontrivial
permutation of the finite menu set); there every `A_c` is null, so the
orbitwise resource fails, while `perfect-gap-zpc-has-finite-readable-translate-algebra`
may still supply a finite atom orbit with a distinct menu at each atom.
