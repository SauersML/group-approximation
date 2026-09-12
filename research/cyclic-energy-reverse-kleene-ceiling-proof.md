---
rg: 2
id: cyclic-energy-reverse-kleene-ceiling-proof
kind: route
title: Search exact matrix energy excess and diagonalize against the HALT ceiling
target: cyclic-energy-reverse-kleene-ceiling-diagonal
requires: []
---

For fixed `e` and `d`, the assertion that `G_e` has a `d`-dimensional exact
unitary representation of energy greater than `b_e` is an existential sentence
over the real closed field. Introduce real and imaginary coordinates for every
entry of every generator matrix. Impose, entry by entry,

```text
U_x^*U_x=U_xU_x^*=I                         (x in X_e),
r(U)=I                                      (r in R_e),
E_e(U)>b_e.
```

After clearing rational denominators, all equalities and the final strict
inequality are real polynomial conditions. In the cyclic case,
`||A||_(2,d)^2=d^(-1)Tr(A^*A)` is a rational polynomial in those coordinates.
Tarski quantifier elimination therefore decides this sentence exactly; no
numerical SDP tolerance is involved.

Let `P_e` test `d=1,2,...` in order and halt at the first dimension for which
the sentence is true. Kleene's recursion theorem gives an index `e_*` whose
behavior is that of `P_(e_*)`.

The machine `e_*` cannot halt. If it did, the exact representation found by
its search would give `beta_(e_*)>b_(e_*)`, while `(EKT1)` would give
`beta_(e_*)<=b_(e_*)`. Hence it does not halt. Since the exact decision at
every earlier dimension terminates, nonhalting means that no dimension carries
an exact representation with energy greater than `b_(e_*)`; consequently

```text
beta_(e_*)<=b_(e_*).                                      (1)
```

Now `(EKT2)` applies. If `G_(e_*)` were hyperlinear, choose a
canonical-profile microstate sequence `U_n`. Expanding every normalized
squared Hilbert--Schmidt norm in `E_(e_*)` gives a finite rational linear
combination of traces of group words. Canonical moment convergence therefore
gives

```text
E_(e_*)(U_n)->Ereg_(e_*)>=a_(e_*).                        (2)
```

On the other hand, `(EKT2)` and `(1)` give

```text
limsup_n E_(e_*)(U_n)<=beta_(e_*)<=b_(e_*)<a_(e_*),       (3)
```

contradicting `(2)`. Thus `G_(e_*)` is the required effectively specified
finitely presented nonhyperlinear group.

For a general recursively enumerable presentation, searching exact
representations of finite relator prefixes is unsound: a tuple may satisfy
every tested prefix and fail a later relator. The required replacement for
Tarski is precisely a uniform semidecision procedure for `beta_e>b_e`.
Effective Higman embedding does not automatically supply it: restriction from
a finite-dimensional representation of the Higman overgroup only proves
`beta_fd(overgroup)<=beta_fd(subgroup)`, while the canonical upper-envelope
hypothesis need not improve from the subgroup ceiling to the overgroup
ceiling.
