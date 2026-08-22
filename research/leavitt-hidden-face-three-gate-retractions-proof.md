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

In the unfolded formal atlas, the literal collision contributes
`n_c=k_0k_1` (the gates are commuting involutions there).  Quotienting by
`psi(n_c)` simply identifies the two formal gates and gives the folded model
used in `(RG2)`.  The folded Tietze map remains injective: a run of equal
`k`-letters has normal form

```text
k^m=s u s^m u s^(-1)        (m != 0),                (RG4)
```

and every join with an `h`-letter exposes a nonidentity base syllable.  Hence
`n_c` supplies no additional normal-closure growth after the fold.  The two
known kernel relations `{n_c,Omega}` reduce exactly to the one-hidden-face
quotient fenced by `(RG3)`.

Nor does the actual corner list provide the relation `Omega` in the other
copy.  It exposes

```text
a_1=u,      r_1=h_0h_1,
x=q_1a_0,   h=a_0p_1,   k=p_0e_1q_0,                 (RG5)
```

but no corner word here isolates `a_0` or `r_0=q_0p_0`.  Producing
`Omega(a_0,r_0)` therefore requires a genuinely new coefficient identity,
not a copy shift of the proved face.

The symbolic artifact verifies `(RG2)`, its nonempty 49-syllable normal form,
and the three exponent specializations in `(RG3)`.  It does not assert that
the whole coefficient factors survive after every relation in `N` is added.
Thus one further independent kernel relation and a one-factor return are the
minimum remaining algebraic requirements.

A literal simultaneous transport would use two degree-zero HNN relations

```text
z^(-1)a_1z=A_0,       z^(-1)r_1z=B_0.                (RG6)
```

These would carry `Omega(a_1,r_1)=1` to `Omega(A_0,B_0)=1`.  They do not arise
as the two lifted relators of a nonsingular one-variable equation by
themselves: if the original exponent sum is `d`, every relator in its
index-`d` Reidemeister--Schreier rewrite has stable-letter exponent `+1`,
whereas each relation in `(RG6)` has exponent zero.  This degree observation
only rules out the literal two-identification encoding; a further gate cell
could still compile the same transport indirectly.
