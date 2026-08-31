---
rg: 2
id: qutrit-head-preserving-three-cycle-router-proof
kind: proof
title: Compute the support-three scalar router, its head compression, and its finite envelope
target: qutrit-first-head-preserving-complete-scalar-router-is-three-cycle
requires:
  - qutrit-mismatched-root-holonomy-proof
  - qutrit-third-cell-head-selector-is-h-centralizer-zero
  - qutrit-head-only-overlap-envelope-is-finite
---

## Simultaneous scalar coordinates

On the leaf fibre with first affine coordinate `u_1`, the qutrit torus
acts on the last coordinate by

```text
J^rZ^s:(u_1,u_2,a) |-> (u_1,u_2,a+r-su_1).
```

Over `F_2`, a three-cycle is the direct sum of one trivial line and the
two-dimensional irreducible order-three module. There are three fibres
for each `u_1` and one extra fixed coordinate. This gives

```text
F_2^28=U_10 direct-sum W_[1,0]^3
            direct-sum W_[1,-1]^3
            direct-sum W_[1,-2]^3.                       (QSA9)
```

The type `[a,b]` has kernel `{J^rZ^s:ar+bs=0}`. Since
`h=J^2Z`, its exponent on the three displayed nontrivial types is,
respectively,

```text
2,                  1,                  0.
```

This proves the fixed-block assertion in `(QSA1)`. It also leaves
untouched complete copies of both `W_0=W_[1,0]` and
`W_1=W_[1,-1]` after choosing one coordinate vector in each.

## Exact intersection of the three-cycle

Let `c_0` be the chosen active trivial coordinate, take coordinate vectors
`d_i in W_i`, and let `g=(c_0 d_0 d_1)`. The support of `g` is disjoint
from the two coordinate summands supporting `H`. Therefore `[g,H]=1`.

The actor does not centralize `h`. Indeed, if it did, then

```text
h d_0=h g c_0=g h c_0=g c_0=d_0,
```

contradicting the fact that a nonidentity order-three operator on `W_0`
has no nonzero fixed vector.

Suppose

```text
c=g c' g^(-1),                    c,c' in C.             (QSA10)
```

Restrict to untouched full copies of `W_0 direct-sum W_1`. The actor is
the identity there, while the restriction of `C` is faithful because the
two type kernels are distinct. Hence `c=c'`. Equation `(QSA10)` now
says that `c` commutes with `g`.

Apply the commutation relation first to `c_0`. Since `C` fixes
`c_0` pointwise,

```text
c d_0=c g c_0=g c c_0=d_0.
```

An element of `C` fixes a nonzero vector of `W_0` only when it acts
trivially on that irreducible module, so `c in ker[1,0]`. Applying the
same relation to `d_0` gives `c d_1=d_1` and hence
`c in ker[1,-1]`. The two kernels intersect trivially. Thus `c=1`,
proving

```text
C intersect gCg^(-1)={1}.                               (QSA11)
```

## Complete Hecke table and the head cut

For characters `chi,psi` of `C`, the finite-subgroup double-coset
formula gives

```text
||z_psi g z_chi||_2^2
 =|C intersect gCg^(-1)|/|C|^2
 =1/81.                                                 (QSA12)
```

There is no compatibility restriction because the intersection is
trivial. Taking `z_chi=e_a` and `z_psi=e_b` proves the first row of
`(QSA4)`.

The head `H` commutes with both `C` and `g`. It is not scalar, so
`<H> intersect <C,g>={1}`. Consequently

```text
<C,g,H>=<C,g> times <H>.
```

The canonical trace on this finite direct product factors. Since
`E=(1-H)/2` has trace `1/2`,

```text
||e_b g E e_a||_2^2
 =tau(E)||e_b g e_a||_2^2
 =1/162.                                                (QSA13)
```

The two summands in `e_2gER` have orthogonal right supports, so
`(QSA13)` gives

```text
||e_2gER||_2^2=2/162=1/81.
```

Also

```text
tau(ER)=(1/2)(2/9)=1/9,
tau(Ee_2)=(1/2)(1/9)=1/18.
```

Because `E` commutes with `g` and every `e_a`, the operator
`A=e_2gER` has right support below `ER` and left support below
`Ee_2`. The two support projections of its polar have equal trace.
Therefore the polar source has trace at most `1/18`. It cannot cover the
`1/9` source `ER`.

This is an exact absence of a full-source relation, not an asymptotic
estimate. The group `<C,g>` is a subgroup of the finite scalar group
`GL_28(F_2)`, and adjoining the commuting involution `H` remains finite.
Alternatively, every entry lies in

```text
A_(Q_0)=F_2[Q_0] isomorphic to F_2 times F_2,
```

so the whole packet embeds in
`EL_28(A_(Q_0)) isomorphic to GL_28(F_2) times GL_28(F_2)`.
Its left regular representation realizes all the displayed traces and
blocks literally.

## Why support two cannot do the coupled job

Let `s=(c_0 d)` be a coordinate transposition with
`d in W_[a,b]` in the moving block. The untouched faithful summands in
the preceding argument again force `c=c'` whenever
`c=sc's^(-1)` with `c,c' in C`. Commuting with `s` is then equivalent
to fixing `d`, and hence

```text
C intersect sCs^(-1)=ker[a,b],                           (QSA14)
```

an order-three line.

For the two available moving types, the kernels are

```text
ker[1,0]=<Z>,                 ker[1,-1]=<JZ>.
```

The selected characters satisfy

```text
chi_a(Z)=omega^a,             chi_a(JZ)=omega^(1+a).
```

Their restrictions to either line are pairwise distinct. Thus
`e_bse_a=0` for `a!=b`: a transposition touching the active trivial
coordinate is diagonal on the proper qutrit row.

A transposition between one `W_0` coordinate and one `W_1` coordinate
can have trivial intersection, but its support is wholly in the moving
block. It commutes with every matrix supported on the `h`-fixed block,
including all of `G_3`. It is therefore only a finite scalar side packet.
The three-cycle is the first coordinate permutation which simultaneously
touches the active block, avoids the head support, and has trivial
intersection.

## The enlarged Leavitt subgroup is still a proper block group

Let `mathcal W` be the `C`-invariant coordinate sum generated by the
active support and the chosen copies of `W_0,W_1`. The group `G_3`,
the torus `C`, and the actor `g` all preserve `mathcal W` and its
coordinate complement. The complement is nonzero: each moving type had
three multiplicity copies and only one was used.

It follows that

```text
<G_3,C,g> != EL_28(L).                                  (QSA15)
```

The subgroup still contains the unchanged full
`G_3=EL_4(L)` Leavitt core, so it remains nonsofic; no residual-finiteness
claim is made for the whole enlarged subgroup. What is finite is the
complete local head/router package, and that is enough to refute a Hall
argument using only `C,g,H`.

To escape `(QSA15)` one needs another actor reaching the unused
multiplicity copies, or an actor touching a head coordinate. In the
latter case the Steinberg formula replaces `H` by a product with a new
`Q_0`-root, so the next calculation must use that new return rather than
the finite head envelope alone.
