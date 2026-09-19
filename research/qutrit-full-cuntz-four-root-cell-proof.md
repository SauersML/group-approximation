---
rg: 2
id: qutrit-full-cuntz-four-root-cell-proof
kind: route
title: Compute the 256-element Cuntz cell and its finite-amalgam shadow
target: qutrit-four-root-cell-finite-but-generates-full-leavitt
requires:
  - qutrit-first-infinite-prefix-holonomy-is-dihedral-amenable
  - amenable-edge-cycles-cannot-create-an-lcs-gap
  - d-ary-leavitt-groups-nonsofic-over-finite-fields
---

## The four coefficient spaces

Work first in the `h`-normal basis. Define additive coefficient spaces

```text
S=span_(F_2){s_0,s_1},
T=span_(F_2){t_0,t_1},
P=span_(F_2){s_r t_s: r,s in {0,1}}.                   (QFC7)
```

The first two spaces have dimension two. The four elements in the last
space are linearly independent: if

```text
sum_(r,s) c_(rs)s_r t_s=0,
```

then multiplying on the left by `t_a` and on the right by `s_b`
gives `c_(ab)=0`. They are matrix units,

```text
(s_r t_s)(s_a t_b)=delta_(sa)s_r t_b,
```

and their diagonal sum is the identity:

```text
s_0t_0+s_1t_1=1.                                       (QFC8)
```

Thus `P` is a copy of `M_2(F_2)` whose identity is the coefficient
`1` in the full Leavitt algebra.

For `u in S`, `v in T`, and `w in P` put

```text
X(u)=x_(ij)(u),       Y(v)=x_(jk)(v),       Z(w)=x_(ik)(w).
```

Root additivity and the Steinberg relation give

```text
[X(u),Y(v)]=Z(uv),
[Z(w),X(u)]=[Z(w),Y(v)]=1.                              (QFC9)
```

Consequently every word in the four generators has a normal form

```text
X(u)Y(v)Z(w),             u in S, v in T, w in P.       (QFC10)
```

As a three-by-three block, this matrix is

```text
I+uE_(ij)+vE_(jk)+(uv+w)E_(ik).
```

Its three displayed entries recover `u,v,w`, so the normal form is
unique. Therefore

```text
|N|=|S||T||P|=2^2 2^2 2^4=256.                         (QFC11)
```

The four commutators `Z_(rs)=Z(s_rt_s)` generate the center. Equation
`(QFC8)` proves

```text
Z_(00)Z_(11)=Z(1)=A,
```

which is the promised full-Cuntz scalar return.

## Scalar intersection

Suppose an element in the normal form `(QFC10)` belongs to
`K=GL_28(F_2)`. Its `(i,j)` and `(j,k)` entries force `u=v=0`,
because no nonzero element of `S` or `T` is scalar. It is then `Z(w)`.
The matrix-unit algebra `P` meets the scalar coefficient field in

```text
P intersect F_2={0,1}.
```

Indeed its identity is `1` by `(QFC8)` and its other fourteen nonzero
elements are non-scalar matrix-unit combinations. Hence

```text
N intersect K={1,A}=<A>.                                (QFC12)
```

Conjugating the whole calculation by the scalar matrix `P_h` preserves
the order, intersections, and equations.

## Qutrit character action

All active indices lie in the `h`-fixed block, so `N` centralizes
`h`. The indices `i,k` are in trivial `C`-summands, while `j` is in
a nontrivial summand. For `U_r=X(s_r)`, conjugating `J` adds a nonzero
degree-one cross-block term. For `V_r=Y(t_r)` it adds a nonzero
degree-minus-one cross-block term. The quadratic terms vanish because
the scalar `J` matrix has no entries between the two isotypic
summands. Thus none of the four roots normalizes `C`.

Each group `C intersect vCv^(-1)` contains `<h>`. If it were larger,
the two order-nine groups would be equal and `v` would normalize `C`.
Therefore the intersection is exactly `<h>`. Character compatibility
on `h=J^2Z` is

```text
2alpha'+beta'=2alpha+beta,
```

and the squared block norm is `3/81=1/27`. This proves `(QFC4)`.

Every `Z(w)` acts only between the two trivial `C` multiplicity
coordinates `i,k`. It therefore commutes with all of `C`, not merely
with `h`. In particular the two sides of `(QFC2)` act diagonally on
all nine character atoms. The relation equates central multiplicity
involutions and imposes no inequality among their character ranks.

## Scalar closure is the full elementary group

Let `G=<K,N>`. The group `K` contains scalar Weyl elements which move
a root position `(a,b)` to any other ordered pair. Hence `G` contains

```text
x_(ab)(s_0), x_(ab)(s_1), x_(ab)(t_0), x_(ab)(t_1)
```

for every `a!=b`. With a third index, Steinberg commutators multiply
coefficients; root additivity adds them. Since the four displayed
coefficients generate `L` as an `F_2`-algebra, `G` contains
`x_(ab)(r)` for every `r in L` and every ordered root position. These
roots generate `EL_28(L)`, while all original generators already lie
there. Thus

```text
G=EL_28(L).                                              (QFC13)
```

This also proves that the four-root threshold has no smaller
scalar-closed continuation.

## The finite-amalgam shadow and its kernel

Let

```text
H=<h> times N,             E=<h,A>.
```

The product is direct because `N` is a two-group, `h` has order three,
and `N` centralizes `h`. Equation `(QFC12)` gives

```text
H intersect K=E.
```

The inclusions therefore define a surjection

```text
K *_E H -> <K,N>=EL_28(L).                               (QFC14)
```

The left group is the fundamental group of one finite edge joining two
finite vertices. It is virtually free and residually finite, and hence
sofic and hyperlinear.

Its canonical qutrit table is exactly the table already computed. To see
the intersection directly, take `v=U_r` or `V_r`. In the amalgam,
a word `v c v^(-1)` with `c in C` can return to the `K` vertex only
if `c` lies in the edge `E`. Since `C intersect E=<h>` and `v`
centralizes `h`, one gets

```text
C intersect vCv^(-1)=<h>
```

also in the cover. Thus its canonical trace has all weights `1/9` and
all norms in `(QFC4)`, while the regular finite vertex `H` realizes
`(QFC2)` exactly.

Finally, the map `(QFC14)` is not injective. If it were, the target
`EL_28(L)` would be virtually free and in particular sofic. This
contradicts the established nonsoficity of binary Leavitt elementary
groups over `F_2`. This use of nonsoficity identifies a nontrivial
kernel but gives no explicit kernel word and no hyperlinearity
obstruction, since soficity is not quotient-closed.

The exact remaining task is therefore sharply localizable: exhibit a
specific word in this amalgam kernel involving at least two
`K`-conjugates of `N`, then prove that its qutrit-typed approximate
realization has a positive normalized-Hilbert--Schmidt defect. The
single cell and its full-Cuntz relation cannot do so.
