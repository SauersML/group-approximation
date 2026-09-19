---
rg: 2
id: cartantype-mackey-cocycle-computation-proof
kind: route
title: Lift the sixteen-element stabilizer by elementary words and compute its scalar extension class
target: cartantype-mackey-cocycle-is-pauli-and-locally-absorbed
requires:
  - nonzero-diagonal-clifford-type-closes-all-six-local-cycles
  - finite-projective-sector-groupoids-have-conjugate-absorbers
---

The script `experiments/sl3_mod4_cartantype_mackey.py` enumerates
`SL_3(Z/4Z)` from the six elementary generators while retaining, for every
element, the same elementary word evaluated modulo `16` and its inverse.
Filtering by `gXg^(-1)=X` gives `16` elements.  Direct multiplication shows
that they commute and that every nonidentity element has order two, proving
`(CMC2)`.

For the retained section `s:H->SL_3(Z/16Z)`, compute

```text
c(g,k)=s(g)s(k)s(gk)^(-1)=1+4Y_(g,k),
e(g,k)=tr(XY_(g,k)) mod 4.                               (CMC4)
```

Among the `256` ordered pairs, `158` have `e=0` and `98` have `e=2`.
The congruence system

```text
z_g+z_k-z_(gk)=e(g,k) mod 4                             (CMC5)
```

is solved exactly by reduction modulo two followed by the lift equation;
it is inconsistent, so the cocycle is nontrivial.  Choosing an `F_2` basis
of `H` and evaluating `(e(g,k)-e(k,g))/2 mod 2` gives `(CMC3)`, whose exact
row reduction has rank two.  The standard classification of twisted group
algebras of elementary abelian two-groups then gives projective irreducible
dimension `2^(rank/2)=2`.

Tensoring with the conjugate projective module cancels every scalar in
`(CMC4)`.  Applying the required abstract groupoid absorber proves the
simultaneous fixed-window statement.

