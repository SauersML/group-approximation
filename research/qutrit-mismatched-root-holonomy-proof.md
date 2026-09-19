---
rg: 2
id: qutrit-mismatched-root-holonomy-proof
kind: route
title: Compute the t0-s0 centralizer commutator and its qutrit fibre graph
target: qutrit-first-mismatched-prefix-holonomy-is-d8
requires:
  - qutrit-full-leavitt-prefix-conjugator-realizes-phase-star
  - finite-overgroup-packing-preserves-hyperlinearity
---

## Simultaneous coordinates in the h-fixed block

The scalar permutation module for `C=<J,Z>` is semisimple over `F_2`.
It has ten trivial summands and three copies of each of the three
nontrivial two-dimensional types

```text
[1,0],              [1,-1],              [1,-2],
```

while the fourth type `[0,1]` is absent. For `h=J^2Z`, the type
`[1,1]=[1,-2]` is trivial on `h`. Thus the `h`-fixed block has the
simultaneous decomposition

```text
F_2^16 = F_2^10(trivial C)
         direct-sum V_[1,1]^3.                           (QMH5)
```

Changing the earlier scalar matrix `P_h` inside this block does not
alter the normal form

```text
P_h^(-1)hP_h=I_16 direct-sum (I_6 tensor kappa).
```

Choose distinct basis coordinates `i,k` in the first summand of
`(QMH5)` and a basis coordinate `j` in the second. All three elementary
roots

```text
X=x_(ij)(t_0),       Y=x_(jk)(s_0),       A=x_(ik)(1)
```

commute with the displayed normal form of `h`. Put

```text
x=P_hXP_h^(-1),      y=P_hYP_h^(-1),      a=P_hAP_h^(-1).
```

These are the elements in the claim.

## The returned root and the exact D8

In characteristic two every elementary root is an involution. The
Steinberg commutator formula and the Leavitt relation `t_0s_0=1` give

```text
[X,Y]=x_(ik)(t_0s_0)=A.                                 (QMH6)
```

The root `A` commutes with both `X` and `Y`. Hence every element of
`D=<X,Y>` has one of the eight normal forms

```text
1,A,X,XA,Y,YA,XY,YX,
```

and `(XY)^2=A!=1`. The forms are distinct: `X` has a nonzero
degree-minus-one entry, `Y` has a nonzero degree-plus-one entry, and
`XY` and `YX` have both. Therefore `D` has order eight and is dihedral.

Because `i,k` lie in two copies of the trivial `C`-module, `A` commutes
with the whole scalar action of `C`. It is a nonidentity elementary
transvection in `K=GL_28(F_2)=SL_28(F_2)`. Scalar permutation
conjugates carry it to every elementary transvection, and elementary
transvections generate `K`. Thus the normal closure of `a` in `K` is
all of `K`.

The same degree inspection shows

```text
D intersect K={1,A}.                                    (QMH7)
```

Indeed every one of the other six normal forms has a nonzero homogeneous
entry of degree `1` or `-1`, whereas every matrix in `K` is scalar of
degree zero. Conjugating by `P_h` preserves this conclusion.

## Exact intersections with C

Let `J_h=P_h^(-1)JP_h`. On the two summands in `(QMH5)` it acts as the
identity and as a nontrivial order-three matrix, respectively. Therefore

```text
E_(ij)J_h+J_hE_(ij) !=0,
E_(jk)J_h+J_hE_(jk) !=0.                                (QMH8)
```

There is no quadratic term in either conjugation because the cross-block
matrix entries `(J_h)_(ji)` and `(J_h)_(kj)` vanish. Consequently

```text
XJ_hX^(-1)
 =J_h+t_0(E_(ij)J_h+J_hE_(ij)),
YJ_hY^(-1)
 =J_h+s_0(E_(jk)J_h+J_hE_(jk)).                         (QMH9)
```

The second terms are nonzero of homogeneous degree `-1` and `1`.
Neither conjugate is a scalar matrix, hence neither lies in `C`. Thus
neither `x` nor `y` normalizes `C`.

On the other hand both roots centralize `h`, so `<h>` is contained in
`C intersect vCv^(-1)` for `v=x,y`. Two order-nine groups sharing more
than one order-three line are equal. Equality would say that `v`
normalizes `C`, which `(QMH9)` excludes. This proves `(QMH2)`.

## The fibre Hecke table

For a joint character write

```text
chi_(alpha,beta)(J)=omega^alpha,
chi_(alpha,beta)(Z)=omega^beta.
```

Since `v` centralizes `h`, the Hecke compatibility condition on the
intersection `<h>` is simply

```text
chi_(alpha',beta')(h)=chi_(alpha,beta)(h).
```

As `h=J^2Z`, this is

```text
2alpha'+beta'=2alpha+beta.                              (QMH10)
```

Each fibre of this functional has three characters. The standard
double-coset norm is

```text
|<h>|/|C|^2=3/81=1/27.
```

This proves `(QMH3)`: the atom graph is the disjoint union of three
complete three-by-three bipartite graphs.

## Why the normal-generating return is still absorbed

Equations `(QMH6)` and `(QMH7)` give a canonical surjection

```text
K *_(<a>) D_8 -> <K,x,y>.                               (QMH11)
```

Both vertex groups and the edge group are finite. The abstract amalgam
is therefore hyperlinear by finite, hence amenable, edge permanence.
More concretely, take common multiples of the left regular
representations of `K` and `D_8` so that their restrictions to
`<a>` agree, then identify those edge representations. The scalar
vertex retains the regular `C`-character vector `1/9` and keeps `a` at
normalized Hilbert--Schmidt distance `sqrt(2)` from the identity. The
`D_8` vertex supplies the two exact holonomy involutions on the same
multiplicity space.

Thus even making the commutator a normal generator of the finite scalar
head does not create a local defect. The unexplored kernel of
`(QMH11)` may contain further full-Leavitt relations; injectivity is not
asserted. What is ruled out is the proposed finite package itself:
`(QMH1)`, the atom incidence `(QMH3)`, and scalar-head exactification
are jointly compatible with canonical finite-amalgam microstates.
