---
rg: 2
id: leavitt-hidden-face-three-gate-retractions-proof
kind: route
title: Separate paired-kernel failure from a one-copy KL kernel and retain each base gate
target: leavitt-hidden-face-three-gate-retractions
requires:
  - leavitt-nielsen-collision-has-a-hidden-first-side-relation
---

Use the folded formal corner group, actual corner map, and Tietze map

```text
phi:Q_form -> C=G_0*G_1,
psi:Q_form -> L=(<x>*C_2(y)*C_2(u))*<s>,
N=ker(phi).
```

The pushout kills a corner word `w` precisely when

```text
psi(w) in <<psi(N)>>_L.                               (RG1)
```

For `phi(w)` to witness failure of the original coefficient injection, it is
not enough that it be a nontrivial mixed normal form in `G_0*G_1`.  One needs
`phi(w) in G_i \ {1}` for one `i`, or an explicit consequence of the same
conjugate product with such a one-factor boundary.  This is the algebraic
form of requiring the outer boundary of the paired picture to lie in one
coefficient copy.

For the first hidden relation, write

```text
B=x s x^(-1)s^(-1)y^(-1)s,
R=psi(Omega)=[u,B^2uB^(-2)].                          (RG2)
```

There are homomorphisms

```text
L/<<R>> -> <x>,       L/<<R>> -> C_2(y),
L/<<R>> -> C_2(u),                                    (RG3)
```

defined in each case by retaining the displayed generator and sending
`s` and the other base generators to `1`.  For the first two maps, `B` maps
to `1`; for the last, `B` also maps to `1`, so `R` maps to `[u,u]=1`.
Each map is onto and is the identity on its named cyclic subgroup.  Hence
`x`, `y`, and `u` all survive after the single face `(RG2)` is imposed.

The symbolic artifact verifies `(RG2)`, its nonempty 49-syllable normal form,
and the three exponent specializations in `(RG3)`.  It does not assert that
the whole coefficient factors survive after every relation in `N` is added.
Thus one further independent kernel relation and a one-factor return are the
minimum remaining algebraic requirements.
