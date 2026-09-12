# Order-three norm feedback: rigidity and exact corner equivalence

Date: 2026-09-08. Let G be any group, let t have order three, and
put e=1+t+t^2 in R=F_2[G]. Then the following are equivalent:

1. The corner ring eRe is directly finite.
2. Every injective scalar Boolean quadratic cellular automaton

       F_a(x)=x+a E Q_t(x),
       E=I+R_t+R_t^2,       Q_t(x)=xR_t x,

   is surjective, with a arbitrary in R.

No normality or centrality of <t> is assumed. Under the first
condition, injectivity also forces the rigidity relation

    (1-e)ae=0:

the feedback aE must preserve im E. A local-inverse argument proves
this even when the block dependency graph is infinite and acyclic.
More concretely, every injective nonsurjective F_a yields the
injective nonsurjective corner-linear map B=e+eae on im E.
Conversely, any such corner-linear map with coefficient b yields
an injective nonsurjective norm rule by taking a=b-e.
For finite G the theorem gives a complete classification, stated
below. This is a reduction and a conditional rigidity theorem,
not a proof of direct finiteness. The unrestricted family x+A Q_t
with A(1-E) nonzero is not settled here. No computation was used.

## Exact coordinates and the norm derivative

Write T=R_t, W=im E and V=ker E. The blocks are the right-t orbits
g<t>, each of size three. A W block is one repeated bit, and a V
block is one of the four even-parity triples. Both are compact
G-invariant subspaces. For d in V put

    N(d)=E Q_t(d).

On a V block, N is zero at 000 and one at each of the other three
states. The local G-equivariant involution

    Psi(d,m)=d+m+N(d),       d in V, m in W,

satisfies Q_t Psi(d,m)=m+mT^2d and E Q_t Psi(d,m)=m. These
identities hold without normality of <t>; their direct four-state
verification is recorded in
[the corner theorem](gottschalk-noncentral-order-three-axis-corner-2026-09-08.md).

Define the linear maps

    K=(I-E)aE: W -> V,
    B=E+EaE:   W -> W.

The output coordinates of P=F_a Psi are exactly

    P(d,m)=(d+Km, N(d)+Bm).                           (1)

We use two elementary facts about a single V block. If v is
nonzero, the derivative

    d -> N(d+v)+N(d)

is one at d=0 and d=v, and zero at the other two states. Thus it
takes both bits. If v=0 the derivative is identically zero. In
particular, for every v it is possible to make this derivative
zero. Choices on distinct t-blocks are independent.

## Injectivity forces B to be injective

This implication needs no finiteness or direct-finiteness assumption.
If a nonzero h belongs to ker B, choose d blockwise so that

    N(d+Kh)+N(d)=0.

Equation (1) then gives P(d,0)=P(d+Kh,h), contradicting injectivity.
Therefore an injective F_a always has injective B.

There is also an explicit choice with no blockwise selection:
put v=Kh and use the inputs (Tv,0) and (T^2v,h). Since
v+Tv+T^2v=0 on V and N is unchanged by cyclic rotation, their
outputs in (1) agree.

The coefficient b=e+eae belongs to eRe. The continuous F_2-linear
dual of W is the left ideal Re, and B is dual to right multiplication
by b on Re. If B is injective, this multiplication is onto. Choose
c in Re with cb=e and replace c by ec, obtaining c in eRe with
cb=e. If eRe is directly finite, then bc=e as well, so B is bijective.
This is the corner linear duality, with its convention and proof
also given in the linked artifact.

For the next step we need only assume B bijective. Its inverse is
continuous by compactness and G-equivariant by uniqueness, hence
uniformly local on the constrained subshift W. Changing the input
variable to w=Bm reduces (1) to the local injective map

    P_L(d,w)=(d+Lw, N(d)+w),       L=KB^-1.           (2)

The map L:W -> V is linear, G-equivariant and local.

## An exact collision test

For h in W, consider the two inputs (d,w) and (d+Lh,w+h). Their
first outputs in (2) agree, and their second outputs agree exactly
when

    N(d+Lh)+N(d)=h.                                  (3)

By the block derivative facts, equation (3) is solvable for a given
nonzero h exactly when

    h_i=1 implies (Lh)_i != 0                        (4)

on every block i. A zero (Lh)_i forces h_i=0, while a nonzero
(Lh)_i permits either required bit. Every collision has this form:
equality of the first outputs forces the d-coordinate difference
to be Lh, where h is the w-coordinate difference. If h=0 the
inputs coincide.

When (4) holds, a canonical solution of (3) is

    d=(1+h) T(Lh).

On an inactive block its two norm arguments are T(Lh) and T^2(Lh),
which have equal norm. On an active block they are zero and the
nonzero vector (Lh)_i, giving derivative one.

Construct a directed graph on the set of t-blocks by placing an
edge j -> i precisely when the coefficient

    L_ij: F_2 -> V_i

is nonzero. Its value at 1 is a nonzero even-parity triple. The
graph has finite propagation because L is local. Its nonzero-edge
relation is G-invariant: translating a V fiber can rotate its
triple, but preserves whether the coefficient vanishes. G acts
transitively on the vertices.

Any finite directed cycle contradicts injectivity. Choose a cycle
of minimum length; a loop is allowed and already has length one.
There are no other edges among its vertices, because any such edge
would close a shorter directed cycle. For the indicator h of its
vertex set, each active row (Lh)_i is exactly the nonzero coefficient
from the predecessor of i. There is no cancellation. Condition
(4) holds and supplies an exact collision. At inactive vertices the
required derivative bit is zero, which is always attainable.

## Long paths contradict the local inverse

It remains to exclude a nonempty acyclic graph, including on an
infinite group. Since the graph is transitive, existence of one
edge gives every vertex at least one incoming edge. Fix a terminal
block i_0 containing the identity of G. Repeatedly choosing a
predecessor gives infinitely many distinct ancestors of i_0:
a repeated vertex would give a directed cycle.

Because P_L is a continuous injection from a compact space into a
Hausdorff space, its inverse on its image is continuous. The bit
w(1) of this inverse has a finite determining set S of output
sites: if two image configurations agree on both output coordinates
at S, their preimages have the same w(1). This follows by compactness
and the finite alphabet; surjectivity is not required. We use only
this finite set, with no metric or finite-generation assumption on G.

Only finitely many t-blocks meet S. Choose an ancestor block i_*
disjoint from S and distinct from i_0, and choose a shortest directed
path from i_* to i_0. This path has no additional edges between its
vertices. A forward chord would shorten the path, while a backward
chord or a loop would create a directed cycle.

Let h be the indicator of the path's vertices. On every active
vertex except i_*, the vector (Lh)_i is the one nonzero contribution
from its predecessor. At i_* it is zero, because no active vertex
has an edge into i_*. Therefore it is possible to choose d
blockwise so that

    N(d+Lh)+N(d)=h+1_(i_*).                          (5)

On the first block both sides are zero. On every other active
block the required bit is one and the derivative can attain it.
On inactive blocks the required bit is zero and is always attainable.

Now the inputs (d,0) and (d+Lh,h) have identical first outputs
under (2), and their second outputs differ exactly by 1_(i_*),
the W configuration supported on the first block. They agree at
every site in S. Their input w bits at the terminal block i_0,
however, differ by one. This contradicts the determining property
of S.

Thus an injective P_L has no edges at all, so L=0. Since B is
bijective, K=LB=0. We have proved the following conditional rigidity
statement without any ring assumption:

    F_a injective and B bijective imply (1-e)ae=0.    (6)

## The exact direct-finiteness equivalence

Suppose eRe is directly finite and F_a is injective. The preceding
steps make B bijective and K=0. Equation (1) becomes
(d,m) -> (d,N(d)+Bm), and conjugating its output by Psi gives

    Psi F_a Psi=(I-E)+B.                             (7)

The right side is identity on V and bijective on W, proving F_a
surjective. This proves assertion 1 implies assertion 2.

Conversely, suppose assertion 2 holds. Let b,c in eRe satisfy cb=e,
and choose a=b-e. Then aE=a, K=0, and the W coefficient in (1)
is b. Formula (7) conjugates F_a to identity on V and B_b on W.
It has a left inverse, namely identity on V and B_c on W, so F_a
is injective. Assertion 2 makes it onto. A surjective map with a
left inverse has that same right inverse; hence B_b B_c=I on W.
The corner action on W is faithful, giving bc=e. Indeed an element
of the corner acting as zero on W induces zero right multiplication
on Re, and evaluation at e makes the element zero. Thus eRe is
directly finite, as required.

## Explicit counterexample extraction in both directions

No direct-finiteness assumption is needed for the following reduction.
If F_a is injective and nonsurjective, B=e+eae is injective by the
kernel argument. If B were surjective, it would be bijective;
conditional rigidity (6) and conjugacy (7) would then make F_a
bijective. Therefore B is also nonsurjective. Extending B by identity
on V gives the explicit scalar linear injective nonsurjective CA

    (I-E)+B=I+EaE

on the original configuration space F_2^G.

Conversely, if a corner-linear map B_b on W is injective and
nonsurjective, choose a=b-e. Then (7) conjugates F_a to identity
on V and B_b on W, so F_a is injective and nonsurjective. Thus the
norm family and the corner-linear family admit counterexamples
exactly together, with explicit constructions in both directions.

## Finite classification and scope

For finite G the corner is finite-dimensional, hence directly
finite. Consequently the exact finite classification is

    F_a bijective
      iff (1-e)ae=0 and e+eae is a unit of eRe.        (8)

Sufficiency follows from (7), and necessity from the theorem and
the corner duality. More generally, direct finiteness of F_2[G]
implies that of its corner, so it suffices for all the norm-feedback
rules considered here. If <t> is normal, the corner is isomorphic
to F_2[G/<t>], as established in the linked artifact.

In particular, a finite reversible example with (I-E)AE nonzero,
if one exists for unrestricted feedback x+A Q_t, must have
A(1-E) nonzero. The extra non-norm feedback produces terms absent
from (1); the rigidity proof does not apply to those terms. For
arbitrary G, we likewise do not assert unconditional preservation
of W from injectivity alone: equation (6) requires B bijective,
which the theorem obtains from direct finiteness of the corner.
