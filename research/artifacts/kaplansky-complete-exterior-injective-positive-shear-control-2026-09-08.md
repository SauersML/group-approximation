# A complete exterior-square injection that still cannot split

Date: 2026-09-08. Exact positive representation control and an
independent finite-representation obstruction. No computation is used.
This does not construct a group-ring split or solve Kaplansky's
conjecture.

The point is to distinguish a proof of injectivity on the **entire**
natural exterior-square source from the much stronger identity
`L P_0[g]f_0=f_0` in a group algebra. The former holds for the actor
below; the latter is impossible.

## 1. The binary coordinate shears

Let `B` be the free binary vector space on actual infinite binary
tails. The operators `s_0,s_1` prepend their respective digits, and
the four binary root coordinates encode `F_4^2` as in
[the complete two-sector artifact](kaplansky-full-two-sector-relative-transporter-obstruction-2026-09-08.md).
Put

```
a=[[1,s_0],[0,1]],       b=[[1,s_1],[0,1]],
g=diag(a,b).
```

Both shears are their own inverses in characteristic two, so these
are genuine binary Leavitt units. Their field-character blocks are

```
A=1+s_0,       B=omega^2 s_0,
C=1+s_1,       D=omega^2 s_1.
```

The relative operator `b^-1a` has character blocks

```
R=1+s_0+s_1,       T=omega^2(s_0+s_1).
```

Both are injective on the free boundary module. The operator
`s_0+s_1` sends a nonzero finite-support vector to a vector with
exactly twice as many support points. Its two prefix ranges are
disjoint and each prefix map is injective. It is therefore injective;
it also cannot fix a nonzero finite-support vector. This proves
injectivity of `T` and `R`, respectively.

## 2. Reduction of the complete source test to one map

Work over `B_4=F_4⊗_(F_2)B` and let `alt` be the exterior quotient.
On `B_4 tensor B_4` define

```
L=alt((1+s_1) tensor (1+s_0)),
M=alt(s_1 tensor s_0),
N=L+M=alt(I tensor I+s_1 tensor I+I tensor s_0).
```

The complete two-sector formula becomes

```
Phi_g(X,Y)=(LX+omega^2 MY, omega MX+LY).               (1)
```

The map `M` is injective: its two tensor factors land in the
disjoint prefix-one and prefix-zero spaces, whose exterior cross
term is their tensor product.

More decisively, put `Z=X+omega^2 Y`. Substitution in (1) gives
the exact equivalence

```
Phi_g(X,Y)=0  iff  NZ=0 and NY=omega MZ.              (2)
```

We prove below that `N` is injective on all finite tensors over the
genuine boundary basis. Equation (2) will then force `Z=Y=X=0`.

## 3. Finite support of a hypothetical kernel

Suppose `NX=0` for a nonzero finite tensor `X`. Let `F` and `H` be
its first-factor and second-factor support sets, respectively, and
put `S=F union H`. Thus every point in `F` occurs with a nonzero row
coefficient of `X`, and every point in `H` occurs with a nonzero
column coefficient.

We first show

```
s_1 F subset S,       s_0 H subset S.                (3)
```

If `xi∈F` and `s_1 xi` were outside `S`, choose `eta` with a nonzero
coefficient of `xi tensor eta` in `X`. The output wedge
`(s_1 xi) wedge eta` has a new endpoint outside `S`. It cannot arise
from the unshifted tensor term, and its new endpoint starts with
one, so it cannot be created by `s_0`. Among the `s_1` terms its
coefficient is unique, by injectivity of prefixing and because an
old endpoint always belongs to `S`. The endpoints are distinct,
so the wedge is nonzero. This contradicts `NX=0`. The argument for
the other inclusion is identical, with the prefix digits reversed.

The two sets in (3) are disjoint, and have cardinalities `|F|,|H|`.
Thus

```
|F|+|H|<=|S|=|F|+|H|-|F intersection H|.
```

It follows that `F,H` are disjoint and that (3) exhausts `S`. Hence
the map

```
h(xi)=s_1 xi for xi∈F,
h(eta)=s_0 eta for eta∈H
```

is a permutation of the finite set `S`.

## 4. The matrix contradiction

Represent `X` as a matrix on the finite coordinate space `F_4^S`,
with first tensor coordinates indexing rows and second coordinates
indexing columns. Its support is in `F x H`. Let

```
Q=X+X^transpose,       P=diag(1_F).
```

The cross supports are disjoint, so `Q` is nonzero and every
coordinate in `S` occurs in its support. Since `h` agrees with
`s_1` on first-factor support and with `s_0` on second-factor support,
symmetrizing the kernel equation gives

```
Q+hQ+Qh^transpose=0.                                (4)
```

Here `h` also denotes the permutation matrix. The bipartite support
of `Q` gives a second identity,

```
PQ+QP=Q.                                            (5)
```

Let `U=im Q`. Equation (4) implies `hU subset U`; finite dimension
and invertibility of `h` make this equality. Equation (5) implies
`PU subset U`. Therefore `U` is invariant under every diagonal
projection

```
P_j=h^j P h^-j,       j>=1.
```

These projections distinguish every point of `S`. Indeed, since
`h` prepends one digit, its inverse on `S` is literal deletion of
the first digit. The diagonal value of `P_j` at a tail `xi` is one
exactly when `h^-j xi∈F`; this is precisely the `j`-th binary digit
of `xi`. Distinct infinite tails differ at some finite digit.
Because `S` is finite, finitely many of the `P_j` distinguish all
its points. Products of those projections and their complements
give every individual coordinate projection on `F_4^S`.

All such projections preserve `U`. Each coordinate occurs in `Q`,
so for every coordinate there is a vector in `U` with a nonzero
entry there. Projecting it onto that coordinate proves that every
basis vector lies in `U`. Thus `U=F_4^S`, and `Q` is invertible.

Equation (4) now gives

```
I+h=Q h^transpose Q^-1.
```

The right side is invertible. The left side kills the nonzero
all-ones vector, because `h` is a permutation and the characteristic
is two. This contradiction proves that no nonzero `X` satisfies
`NX=0`.

The proof uses actual distinct binary tails and the literal prefix
maps. Identifying two different infinite tails in a finite model
would invalidate the coordinate-separation step and would not test
this assertion.

## 5. What the positive exterior test proves

Injectivity of `N` and equation (2) prove that `Phi_g` is injective.
The complete-source identification from the earlier artifact then
proves that `P_0[g]f_0` is injective on **all** of `im f_0` in the
scalar-extended natural exterior-square representation.

This assertion allows arbitrary finite tensors in both source
sectors, rather than only determinant lines or decomposable test
vectors. It is still a statement about one representation.

## 6. Independent finite-representation obstruction to the ring identity

The coefficients `s_0,s_1` generate a free positive associative
algebra inside the binary Leavitt algebra. One elementary way to
see their linear independence is to apply distinct finite words
to the tail `1000...`: equality of two resulting prefixed tails
would make this nonperiodic tail fixed by a nonempty prefix word,
which is impossible.

Both `g` and `g^-1=g`, and all constant chart matrices, therefore
lie in

```
GL_4(F_2< s_0,s_1 >).
```

The algebra homomorphism setting both creators to zero induces an
actual finite matrix representation of the subgroup `〈K,g〉`:

```
epsilon:〈K,g〉 -> GL_4(F_2),
epsilon|K=the constant chart,       epsilon(g)=I.
```

Its natural four-dimensional module, after scalar extension, is
`V_+ direct-sum V_-`. Its exterior square is

```
det(V_+) direct-sum (V_+ tensor V_-) direct-sum det(V_-).
```

The reduced source projector acts as one on the two determinant
lines. The target projector acts as zero on both determinant lines
and on the middle, center-trivial sector. Thus, on this actual
finite-dimensional representation,

```
f_0!=0,       P_0=0.
```

Consequently the identity `L P_0[g]f_0=f_0` is impossible in the
subgroup algebra. Conditional expectation onto that subgroup
algebra handles an inverse allowed anywhere in the ambient group
algebra. No extension of this finite representation to all binary
Leavitt units is required.

The actor therefore supplies an exact paired control: the complete
natural exterior-square source test passes, while a different
finite representation rules out the group-ring split. The headline
comparison remains unresolved for actors outside the established
obstructions.
