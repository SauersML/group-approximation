# A seven-cell finite core and one missing Thompson completion equation

2026-09-08. Written group and binary-prefix calculations. The construction
below is an explicit sufficient architecture with proved obstructions on
its missing generator. It is not a solved packet. No
local code, build, search, or new Lean verification is asserted.

## 1. Conventions and the exact finite core

Use ordinary left actions: in `XY`, `Y` acts first. Write
`[X,Y]=XYX^(-1)Y^(-1)` and `gamma(X)=CXC^(-1)`.
The symbol `X^T` in a Thompson relator instead means `T^(-1)XT`.

Label seven clopen prefix cells by the nonzero vectors of `F_2^3`:

| Cell label | Vector label | Binary prefix |
| --- | --- | --- |
| `a` | `100` | `000` |
| `b` | `010` | `001` |
| `c` | `001` | `010` |
| `d` | `110` | `011` |
| `e` | `101` | `100` |
| `f` | `011` | `101` |
| `g` | `111` | `11` |

Vector labels specify the finite permutation action; the last column
specifies the actual complete binary prefix code. They are different
labellings. For example, `c0` means binary prefix `0100`, and
`c alpha` denotes an arbitrary point of the cell labelled `c`.

Every permutation of the seven cells preserves the remaining infinite
tail and is an element of `V`. Define

```text
C=(a b c)(d f e),             Y=(b d)(f g),
b_1=Y,                       b_2=Y.                 (1)
```

These are the natural actions of the coordinate cycle `(123)` and
`x_12(1)` on the nonzero vectors of `F_2^3`. They generate the natural
`SL_3(F_2)` action: cyclic conjugation gives roots `12,23,31`, and
their three-distinct-index commutators give the other three roots.
Elementary row reduction generates all invertible matrices. Their
number is `(8-1)(8-2)(8-4)=168`, and every determinant is one.

To avoid confusion with cell labels, put hats on the constant compiler
words corresponding to its `d,h,a,e`. Direct elementary multiplication
gives

```text
d_hat=[Y,gamma(Y)]       =x_13(1)=(c e)(f g),
h_hat=gamma^2(d_hat)     =x_32(1)=(b f)(d g),
a_hat=[d_hat,h_hat]      =x_12(1)=Y,
e_hat=gamma(d_hat)       =x_21(1)=(a d)(e g),
A=a_hat e_hat a_hat^(-1)         =(a b)(e f),
D=gamma^2(A)                     =(a c)(d f),
p_0=gamma(Y)            =x_23(1)=(c f)(e g),
q_0=[gamma^2(Y),a_hat]   =x_32(1)=(b f)(d g),
X_0=p_0 q_0 p_0                  =(b c)(d e).       (2)
```

Here `gamma^2(X)=C^(-1)XC` since `C^3=1`. In particular
`d_hat^2=(AC)^2=1` and `DA=C`. These are exact finite group
identities, independent of the still unknown third involution.

## 2. A diagonal Thompson copy with these same anchors

Use the authenticated source generators from the
[native Thompson certificate](leavitt-explicit-thompson-c-killing-certificate-2026-09-08.md):

```text
A_V=swap(00,01),
B_V=swap(01,10) swap(01,11),
D_V=swap(1,00).                                      (3)
```

As ordinary left maps the written product for `B_V` sends
`01 alpha -> 11 alpha -> 10 alpha -> 01 alpha`.
This is the same written product that represents the source's
right-acting generator by its inverse, as checked in that certificate.

Let `eta_1` be the finite-prefix homeomorphism from the whole Cantor
space onto `[a] disjoint-union [b] disjoint-union [c]` given by

```text
00 alpha -> a alpha,  01 alpha -> b alpha,  1 alpha -> c alpha.
```

Define `eta_2` in the same way with target labels `(f,e,d)`.
For every `v in V`, act by `eta_i v eta_i^(-1)` on each of these
two clopen regions, and act as the identity on `[g]`. Their finite
prefix tables glue to an element `iota(v) in V`. This is an injective
homomorphism, because restriction to the first region detects `v`.
The `eta_i` are partial homeomorphisms onto their indicated regions;
they are not being treated as global elements of `V`.

The images of `A_V,D_V,D_V A_V` are precisely `A,D,C` in (1)--(2).
The second generator is

```text
B_0=iota(B_V)
   =swap(b,c0) swap(b,c1) swap(e,d0) swap(e,d1).       (4)
```

The two pairs of swaps have disjoint regions of support. Thus `B_0`
fixes `[a],[f],[g]` pointwise and, in particular,

```text
B_0(e alpha)=d1 alpha.                              (5)
```

All eight authenticated Thompson presentation words vanish at
`(A,B_0,D)`. This follows from the injective homomorphism just
constructed, rather than an assumed extension of the finite core.
The finite core and this copy of `V` really are subgroups of the same
target `V`, sharing the prescribed `S_3=<A,C>`.

## 3. The one missing compiler equation

Let `Z in V` satisfy `Z^2=1` and `ZY=YZ`. For this paragraph only,
define the remaining actual compiler words by

```text
U(Z)=[Y,C Z C^(-1)],
P_1(Z)=[e_hat,U(Z)],
Q_1(Z)=[C^(-1) Z C,Y],
beta(Z)=X_0 P_1(Z) Q_1(Z) P_1(Z).                   (6)
```

The repeated last `P_1(Z)` is intentional; it is not its inverse.
These are exactly `u,p_1,q_1,X_0 X_1` in the shared compiler after
substituting `(C,Y,Y,Z)`. No coefficient identity or extra involution
law on `P_1` is used.

**Sufficient completion criterion.** A commuting involution `Z`
satisfying

```text
beta(Z)=B_0                                          (7)
```

gives a homomorphism

```text
Q=(C_3*C_2^3)/<<T_8>> -> V,
(c,b_1,b_2,b_3)       |-> (C,Y,Y,Z),                 (8)
```

and this homomorphism retains `c`.

Indeed the marked factor laws hold, (2) gives the square anchors,
and (7) turns all six retained Thompson rows into the exact rows at
`(A,B_0,D)`. The two other Thompson rows also hold. The image of `c`
is the nonidentity order-three permutation `C`.

The use of `b_1=b_2` is allowed for (8); (8) is not asserted injective
on the marked second factor. Once (8) exists, the
[eight-cell wreath normalization](leavitt-eight-tail-wreath-normal-form-2026-09-08.md)
constructs a new map retaining `c` and embedding that factor by its
regular bit-flip action. This normalization is conditional on an
actual solution of (7), not a substitute for one.

Equation (7) is a sufficient construction with a prescribed diagonal
copy. It is not asserted equivalent to the existence of an arbitrary
homomorphism `Q->V` or `N->V`.

## 4. All commuting involutions in this architecture

The fixed and moved regions of `Y` are

```text
F=[a] disjoint-union [c] disjoint-union [e],
M=[b] disjoint-union [d] disjoint-union [f] disjoint-union [g].
```

Every element centralizing `Y` preserves `F` and `M`, because it
preserves the fixed-point set of `Y`. Put `T=[b] disjoint-union [f]`.
Identify `M` with `F_2 x T` by sending `(epsilon,t)` to `Y^epsilon(t)`.
In these coordinates `Y(epsilon,t)=(epsilon+1,t)`.

The full list of involutions in `C_V(Y)` is given by the following
data:

* an involution `v` in the prefix-replacement group `V(F)`;
* an involution `h` in `V(T)`;
* a locally constant function `kappa:T->F_2` satisfying
  `kappa(h(t))=kappa(t)`.

Their action is `v` on `F` and

```text
Z(epsilon,t)=(epsilon+kappa(t),h(t))                 (9)
```

on `M`. Here order dividing two is allowed, and `V(F),V(T)` mean
finite-prefix homeomorphisms of the indicated clopen spaces.

For necessity, pass a commuting map to the quotient of `M` by `Y`.
Its image is `h`; whether a representative from `T` lands in `T` or
in `YT` gives the bit `kappa`. Finite prefix tables make that bit
locally constant and make `h` a finite-prefix homeomorphism. Squaring
(9) gives `(epsilon+kappa(t)+kappa(h(t)),h^2(t))`, proving the two
conditions. Conversely these conditions give an involution commuting
with `Y`. The finitely many clopen pieces of `kappa` and the finite
tables of `v,h` glue to a finite table in `V`. Thus no commuting
involution has been omitted from this parametrization.

## 5. A completion must act on the moved region

**Obstruction.** No solution of (7) fixes `M` pointwise.

Suppose otherwise, so `Z` is supported on `F`. Conjugation by `C`
sends `F` onto `[a] disjoint-union [b] disjoint-union [d]`. The
involution `Y` preserves this latter region. Consequently `U(Z)`
is supported there. The constant `e_hat=(a d)(e g)` also preserves
it, so `P_1(Z)` is supported there too. In particular `P_1(Z)` fixes
`[e],[f],[g]` pointwise.

Since both `X_0` and `B_0` fix `[f]`, equation (7) implies
`Q_1(Z)` fixes `[f]`. Write `Z'=C^(-1)ZC`, so `Q_1=Z'YZ'Y`.
For any point `f alpha`, read this product from right to left:

```text
f alpha --Y--> g alpha --Z'--> g alpha
        --Y--> f alpha --Z'--> C^(-1) Z(e alpha).    (10)
```

The second arrow is fixed because `C` and `Z` both fix `[g]`.
Thus fixation of `[f]` in (10) forces `Z(e alpha)=e alpha` for
every `alpha`.

Now `Z` is supported on `[a] disjoint-union [c]`, so `Z'` is
supported on `[b] disjoint-union [c]`. Conjugating this last support
by `Y` gives `[d] disjoint-union [c]`. Hence `Q_1` is supported on
`[b] disjoint-union [c] disjoint-union [d]` and fixes `[e]`.
Both occurrences of `P_1` also fix `[e]`. Therefore

```text
beta(Z)(e alpha)=X_0(e alpha)=d alpha,               (11)
```

contrary to (5). For example, take any tail beginning in `0` to
distinguish these images. This proves the obstruction.

In the parametrization (9), the excluded subclass is exactly
`h=id_T, kappa=0`. A successful completion must have nontrivial
quotient motion, a nonzero bit function, or both. This does not
exclude the remaining centralizer data.

## 6. Nonreversibility forces a noninvolutive compiled p1

There is a further obstruction that applies to every completion of
(7), not only to the subclass excluded in Section 5. Put

```text
R=X_0 B_0.
```

Because `X_0^2=1`, equation (7) is precisely

```text
R=P_1(Z) Q_1(Z) P_1(Z).                             (12)
```

The exact prefix action of this required map is

```text
b alpha  -> b1 alpha,       e alpha  -> e1 alpha,
c1 alpha -> b0 alpha,       d1 alpha -> e0 alpha,
c0 alpha -> c alpha,        d0 alpha -> d alpha.      (13)
```

It fixes `[a],[f],[g]` pointwise. The same orientation of the
diagonal action on the two triples is essential in (13).

**Lemma.** The map `R` is not conjugate to `R^(-1)` by any element
of Thompson's `V`.

For a prefix map `v` whose local rule at a point `xi` is
`u alpha -> w alpha`, define its signed prefix-length change by

```text
ell(v,xi)=|w|-|u|.
```

This does not depend on the table refinement, since refining a row
appends the same word to its source and target. Composition gives

```text
ell(vw,xi)=ell(v,w xi)+ell(w,xi).                    (14)
```

In particular if `v xi=xi`, then for any `k in V`,

```text
ell(k v k^(-1),k xi)=ell(v,xi).                     (15)
```

Also every finite-prefix map preserves eventual-tail equivalence:
it replaces only a finite initial word. Hence it sends eventually-one
sequences to eventually-one sequences, and eventually-zero sequences
to eventually-zero sequences. Those two classes are disjoint.

The fixed points of `R` with nonzero signed length change are exactly

```text
point                  ell(R,point)
b 111...                    +1
e 111...                    +1
c 000...                    -1
d 000...                    -1.                     (16)
```

Indeed a fixed point in `[b]` must satisfy `alpha=1 alpha`, and
one in the `c0` branch must satisfy `0 alpha=alpha`. The `c1`
branch moves to another cell. These observations and their `e,d`
counterparts prove the list. All other fixed points lie in the
three pointwise fixed cells and have length change zero.

For the inverse map the same four points are fixed with the signs
reversed. Thus any conjugator from `R` to `R^(-1)` would have to
send `b 111...`, whose sign is `+1`, to `c 000...` or `d 000...`.
Equation (15) requires this sign preservation, whereas eventual-tail
preservation makes either image impossible. This proves the lemma.

Now let `Z` be any involution commuting with `Y`, and abbreviate
`P=P_1(Z)` and `Q_1=Q_1(Z)`. Both `Z'=C^(-1)ZC` and `Y` are
involutions, so

```text
Q_1=Z' Y Z' Y,       Y Q_1 Y=Q_1^(-1).              (17)
```

If `P^2=1`, equation (12) would express `R=P Q_1 P^(-1)`.
Then the involution `P Y P^(-1)` would conjugate `R` to
`R^(-1)`, contrary to the lemma. Therefore every solution of (7)
necessarily has

```text
P_1(Z)^2!=1.                                        (18)
```

This identifies a short additional native relation incompatible with
the whole prescribed architecture. In the original compiler, with
unit length for each occurrence of `c,b_1,b_2,b_3` or its inverse,

```text
|d|=8,       |e|=10,       |u|=8,
p_1=[e,u],  |p_1|=2(10+8)=36,       |p_1^2|=72.     (19)
```

These are unreduced lengths. Equation (5) of the
[native certificate](leavitt-explicit-thompson-c-killing-certificate-2026-09-08.md#2-authenticate-the-compiler-in-the-native-leavitt-group)
proves `q(p_1)=x_23(tv)=x_23(t_1)`. An elementary transvection
in characteristic two squares to the identity. Consequently
`p_1^2` is a true native kernel word, and imposing this additional
row excludes every completion of (7).

The relation `p_1^2=1` is not an explicitly imposed row of `T_8`
and was not assumed in Sections 1--5. No assertion that it cannot
follow from `T_8` is made. The exclusion concerns the prescribed
same-orientation diagonal action and its equation (7); it does not
exclude arbitrary embeddings of `V`, all maps `Q->V`, or all maps
`N->V`. The fixed-germ argument supplies no normalized-HS gap.

## 7. Twisting one component and the necessary multiplicity condition

The nonreversibility argument alone does not survive every change of
orientation. This can be seen by an explicit automorphism of the source
`V`. Let `J` complement every bit of an infinite binary sequence, and
let `w in V` have the finite prefix table

```text
11 alpha -> 00 alpha,   10 alpha -> 01 alpha,   0 alpha -> 1 alpha.
```

Then `kappa=wJ` complements the tail separately after each of the
source code leaves `00,01,1`. It normalizes `V`: `J` sends any
finite-prefix table to the table with both prefixes complemented,
and `w` belongs to `V`. The map `kappa` need not itself belong to
`V`, and is not being used as an internal conjugator. Its action
on the source generators is

```text
kappa A_V kappa^(-1)=A_V,
kappa D_V kappa^(-1)=D_V,
kappa B_V kappa^(-1)=B_V^(-1).                      (20)
```

For the first two identities, `kappa` applies the same tail operation
on every code cell. For the last, it exchanges the two source swaps
`swap(01,10)` and `swap(01,11)`.

Twist only the second component of the diagonal homomorphism in
Section 2 by this automorphism. It still has images `A,C,D`, while
its second generator becomes

```text
B_twist=swap(b,c0) swap(b,c1) swap(e,d1) swap(e,d0).
R_twist=X_0 B_twist.                                (21)
```

This required map is reversed by the involution `M=(b d)(c e)`.
To check this, identify its two support components by the ordered
pairs `(b,c)` and `(e,d)`. Let `X` be the swap of the two cells
and `B` the three-cycle used in (4). The component maps are `XB`
and `XB^(-1)`, while `M` exchanges the components with the leaf
swap `X`. Thus

```text
X(XB)X=B X=(X B^(-1))^(-1),
X(X B^(-1))X=B^(-1) X=(X B)^(-1).
```

Outside these components all three maps fix points. Consequently
`M R_twist M=R_twist^(-1)` exactly.

There is nevertheless a second obstruction: `R_twist` is not a
square in `V`. Its first component retains the three branches in
the left column of (13), whereas its second component has branches

```text
e alpha -> e0 alpha,   d0 alpha -> e1 alpha,   d1 alpha -> d alpha.
```

The four nonzero fixed germs are now

```text
b 111... : +1,       e 000... : +1,
c 000... : -1,       d 111... : -1.                 (22)
```

If `T^2=R_twist` for `T in V`, then `T` commutes with `R_twist`.
By (15) and eventual-tail preservation, it permutes the fixed points
of each specified nonzero exponent in each eventual-tail class.
In particular it must fix `b 111...`, the unique eventually-one
fixed point with exponent `+1`. But (14) would then give

```text
1=ell(T^2,b 111...)=2 ell(T,b 111...),
```

impossible because the length change is an integer. This proves the
square-root obstruction. In a completion with `P_1^2=1`, equation
(12), now with `R_twist` in place of `R`, would make the target
conjugate to `Q_1=(Z'Y)^2`. It would therefore be a square. Hence
the additional native row `p_1^2` excludes the twisted completion
as well, despite its reversibility.

The two arguments give a useful necessary count for repeated diagonal
components. Consider any finite disjoint collection of finite-prefix
copies of the construction, each with either the standard orientation
or the automorphism (20). Suppose the constant `X_0` acts as the
coordinate-`23` swap on every component, as above. Let `n_+` count
the standard components and `n_-` the complemented components, and
let `R=X_0 B` be their combined required map. The counts of nonzero
fixed germs are

| Eventual-tail class | Exponent `+1` | Exponent `-1` |
| --- | --- | --- |
| Eventually one | `n_+` | `n_-` |
| Eventually zero | `n_-` | `n_+` |

Adding finite cell prefixes changes neither the eventual-tail class
nor these exponents. Reversibility of `R` therefore requires
`n_+=n_-` by (15).

If `R=T^2`, then on either finite set of exponent-`+1` fixed points
in the table, the permutation induced by `T` squares to the identity,
because `T^2=R` fixes every point in that set. It has no fixed point:
a fixed point would again require `1=2 ell(T,xi)`. All its cycles
therefore have length two, so both `n_+` and `n_-` are even.

An involutive `P_1` makes the required `R=P_1 Q_1 P_1` both
reversible and a square, since `Q_1` has both properties. Thus every
such completion preserving the native square row necessarily satisfies

```text
n_+=n_-,       n_+ and n_- are even.                (23)
```

In particular, all four orientation choices on the original two
components fail. With at least one component, the first counts not
excluded by (23) are four components, two in each orientation.
Two disjoint copies of the seven-cell finite core provide anchors
on fourteen cells for such a proposed enlargement. This only supplies
anchors and passes these necessary count tests: no compatible `Z`,
completed compiler, or hyperlinear target is constructed.

The argument concerns precisely the finite-prefix diagonal components
and the two orientations just described. It neither classifies all
anchor-sharing copies of `V` nor excludes arbitrary maps from `Q`
or `N` to `V`.

## 8. Scope and exact replay

The first two marked involutions coincide. The finite core and the
Thompson copy already coexist inside the same concrete target `V`,
with their prescribed `S_3` generators equal. Their compatibility
therefore follows from the displayed actions. No embedding of an
abstract amalgam, or retraction from `N`, is assumed or asserted.

The standalone script
[`leavitt_seven_cell_exact_replay.py`](../../experiments/leavitt_seven_cell_exact_replay.py)
checks finite-prefix bijectivity, all constant identities in (2), the
diagonal images in (3)--(4), and all eight Thompson rows at
`(A,B_0,D)`. It performs no search, evaluates no alleged completing
`Z`, and is prepared for a bounded MSI run only. An execution record
is separate evidence; this file does not assert that it has run.

No solution of (7) is supplied. If one exists, it gives a useful
comparison of the packet with `V`. Obtaining a known hyperlinear
target, and thereby disproving a uniform matrix-gap witness through
this construction, would additionally require hyperlinearity of `V`.
That property is neither assumed nor established here. Failure of
this prescribed completion problem would not exclude every map
`N->V`, and would not by itself prove a uniform normalized-HS gap.
