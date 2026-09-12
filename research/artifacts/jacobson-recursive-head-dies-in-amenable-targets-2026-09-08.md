# The recursive head dies in every amenable target

2026-09-08. Let `Gamma=Theta_shift` and let `w=x_13,Q` be its
marked head transvection. Every homomorphism from `Gamma` to an
amenable discrete group kills `w`, and therefore kills the whole
normal closure of the head. This excludes every amenable target
retaining the mark, with no restriction on its chosen representation
or coordinate decomposition.

The conclusion concerns exact homomorphisms into amenable groups.
It does not assert that the mark dies in matrix norm coronas.

## 1. The faithful finitary kernel

Use the presentation and bilateral action from
[the stable-letter construction](jacobson-stable-letter-recursion-and-matrix-gap-2026-09-08.md).
Put

```text
V=F_2^(Z x {1,2,3}),
pi:Gamma -> GL(V).
```

Here vectors have finite support. The
[recursive finite-packet theorem](jacobson-recursive-packets-generate-finitary-linear-kernel-2026-09-08.md)
proves that

```text
L=<K_i : i in Z> = normalClosure_Gamma(w)
```

is normal and that `pi` identifies `L` faithfully with
`GL_fin(V)`: all invertible matrices supported on a finite set of
the displayed coordinates. In particular `w!=1` in `Gamma`.

We first record two elementary consequences of this precise kernel
identification.

**Simplicity.** The group `L` is simple. To see this, identify it
with `GL_fin(V)` and take a nonidentity element `x` of a nontrivial
normal subgroup `N` of `L`. Choose a vector `v` with `xv!=v`.
Choose a coordinate `j` outside the finite supports of `x` and `v`,
and write `epsilon_j` for its coefficient functional. The map

```text
u=I+v epsilon_j
```

is an involutory transvection in `L`. Since `x` fixes the new
coordinate and does not mix it with the old support,
`epsilon_j x^(-1)=epsilon_j`. With `[x,u]=xux^(-1)u^(-1)`,
direct multiplication gives

```text
[x,u]=I+(xv+v) epsilon_j.                              (1)
```

The right side is a nonidentity transvection in `N`. A change of
basis on a sufficiently large finite coordinate set conjugates it
to an elementary transvection `I+E_ab`. Coordinate permutations
then give every elementary transvection. These generate every
finite general linear group over `F_2` by row reduction, hence
generate `L`. Thus `N=L`.

**Centralizer.** The centralizer of `GL_fin(V)` in `GL(V)` is
trivial. Indeed, suppose that an invertible linear map `A` commutes
with every `I+e_i epsilon_j`, for `i!=j`. Subtracting the identity
part gives

```text
A e_i epsilon_j = e_i epsilon_j A.
```

Apply this equality to `e_j`. It implies that `A e_i` is a scalar
multiple of `e_i`. Invertibility makes this scalar nonzero, so over
`F_2` it equals one. This holds for every `i`, and therefore `A=I`.

Consequently the abstract centralizer is exactly

```text
C_Gamma(L)=ker(pi).                                    (2)
```

For the forward inclusion, apply `pi` and the centralizer
calculation. Conversely, if `pi(g)=I`, then for every `l in L`
normality gives `[g,l] in L`, and its literal image is trivial.
Faithfulness on `L` implies `[g,l]=1`.

## 2. Retaining the mark forces the literal image as a quotient

Let `rho:Gamma -> A` be any homomorphism with `rho(w)!=1`.
The subgroup `ker(rho) intersect L` is normal in the simple group
`L` and cannot equal `L`. Hence it is trivial. For `g in ker(rho)`
and `l in L`,

```text
[g,l] in ker(rho) intersect L = {1}.
```

Thus (2) implies

```text
ker(rho) <= ker(pi).                                   (3)
```

In particular the assignment `rho(g) |-> pi(g)` is well defined
and gives a surjective homomorphism

```text
rho(Gamma) ->> pi(Gamma).                              (4)
```

This argument uses the complete normal finitary subgroup. It would
not follow merely from a sequence of commuting finite head groups.

## 3. An explicit nonamenable positive-tail symbol

Let `H=<G_Q,G_P,h>` be the original subgroup of `Gamma`. On all
sufficiently large positive levels, each operator in `pi(H)` is
translation invariant with finite propagation. More explicitly,
for each such operator `a` there are finitely many matrices
`M_k in M_3(F_2)` and a cutoff `N` such that

```text
a e_(j,n) = sum_(i,k) (M_k)_(ij) e_(i,n+k)
                       for every n>=N.                (5)
```

The matrices `M_k` are unique, since the output coordinates in
(5) are distinct for distinct pairs `(i,k)`. Define

```text
sigma(a)=sum_k M_k z^k.
```

Every generator and its inverse has the form (5). Products have
the same form: choose the input level large enough that every
intermediate level also exceeds the next operator's cutoff.
The product coefficients are precisely Laurent matrix
multiplication. Applying this to `a` and `a^(-1)` proves that

```text
sigma:pi(H) -> GL_3(F_2[z,z^(-1)])                     (6)
```

is a group homomorphism. This is the positive-tail version of the
[Jacobson symbol map](../jacobson-shift-faithfulness-proof.md), but
the cutoff argument above proves exactly the homomorphism needed
here without an additional group identification.

The generator symbols follow directly from the bilateral action:

```text
sigma(pi(g_Q))=I,          sigma(pi(g_P))=g,

sigma(pi(h)) = [[0,z,0],
                [z^(-1),0,0],
                [0,0,1]].                              (7)
```

Write `x_ij(r)=I+r E_ij`, and let `w_ij` denote the constant
coordinate swap. The image in (6) contains

```text
d=sigma(pi(h w_12,P))=diag(z,z^(-1),1),

A=w_23 d x_13(1) d^(-1) w_23=x_12(z),
B=x_12(1)x_21(1).                                     (8)
```

Thus `A` and `B` act on the first two coordinates and fix the
third. We now prove that they generate `C_2 * C_3`.

Let `F=F_2((z^(-1)))`, equipped with its nonarchimedean absolute
value normalized by `|z|=2`. Use the usual fractional-linear
action on the projective line over `F`. The matrices in (8) give

```text
A(x)=x+z,
B(x)=1/(x+1),             B^2(x)=(x+1)/x.             (9)
```

In particular `A` has order two and `B` has order three. Set

```text
X_A={x in F : |x|>1},
X_B={x in F : |x|<=1}.
```

These are nonempty disjoint subsets of the projective line, and
the ultrametric inequality gives

```text
A(X_B) <= X_A,
B(X_A) <= X_B,             B^2(X_A) <= X_B.            (10)
```

Indeed `|x+z|=2` for `x in X_B`; and if `|x|>1`, then
`|x+1|=|x|`, so the two images under `B,B^2` have absolute
values `|x|^(-1)` and one, respectively.

For completeness, (10) rules out every additional relation.
A reduced word whose first and last syllables lie in the same
factor maps the other factor's domain into that factor's domain,
so cannot be the identity. Any reduced word is conjugate either
to one syllable or to an alternating word of even length.
After cyclically rotating the latter, it starts with `A` and
ends with `B^j`, where `j` is one or two. Conjugate it by
`B^k`, where `k` is the other nonzero residue modulo three.
The new reduced word starts with `B^k` and ends with the
nonidentity syllable `B^(j-k)`. It therefore maps `X_A` into
`X_B` by (10), and is not the identity. This proves

```text
<A,B> ~= C_2 * C_3.                                    (11)
```

## 4. Why this free product is nonamenable

Here is a short algebraic and graph-theoretic verification. In the
abstract free product `F_0=C_2*C_3`, take the natural surjection
onto `C_2 x C_3` and let `N_0` be its kernel. Form the graph
whose vertices are the left cosets `F_0/C_2` and `F_0/C_3`,
with one edge labelled `g` joining `g C_2` to `g C_3` for each
`g in F_0`. Reduced free-product words show that this connected
graph is a tree: a nonbacktracking cycle would yield a nonempty
reduced alternating word equal to the identity.

The group `N_0` acts freely on the tree. An element fixing a
vertex lies in a conjugate of a factor, and the quotient map
is injective on each such conjugate. The quotient graph has
six edges, three vertices of the first type and two of the
second type; it is the complete bipartite graph `K_(3,2)`.
Choose a spanning tree in this quotient. Lifting that tree
identifies the deck group with the free group on its remaining
edges: each extra edge supplies one generator, and the covering
tree gives no relation. There are

```text
6-(3+2)+1=2
```

such edges. Thus `N_0` is a free group on two generators.

To see directly that the free group on `u,v` is nonamenable,
let `W(s)` be the set of nonempty reduced words beginning with
the letter `s`. Its four sets `W(u),W(u^(-1)),W(v),W(v^(-1))`
partition the group apart from the identity. In a left-invariant
finitely additive probability measure, every singleton in this
infinite group has measure zero. But

```text
u W(u^(-1)) = N_0 without W(u),
v W(v^(-1)) = N_0 without W(v)
```

force each corresponding pair of measures to sum to one. The
four disjoint sets would therefore have total measure two,
a contradiction. This proves nonamenability of `N_0` and hence
of `C_2*C_3`, since subgroups of amenable groups are amenable.

By (11), the image `sigma(pi(H))` is nonamenable. Amenability
passes to homomorphic images and subgroups, so `pi(H)` and
then `pi(Gamma)` are nonamenable.

## 5. The amenable-target conclusion and its scope

If `A` is amenable and `rho:Gamma -> A` retained `w`, its
image would be amenable, while (4) would make the nonamenable
group `pi(Gamma)` a quotient of that image. This is impossible.
Therefore every such homomorphism kills `w`, and the normal
closure identity kills all of `L`.

The result covers arbitrary amenable marked-quotient attempts,
including ones with dense changes of basis or nonnatural finite
packet representations. It leaves open representations into
nonamenable targets and into matrix norm coronas. No conclusion
about the MF status of `Gamma` or its literal image follows from
this amenability obstruction alone.
