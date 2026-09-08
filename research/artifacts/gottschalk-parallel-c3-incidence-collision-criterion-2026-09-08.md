# Parallel C3 complementation: an exact incidence criterion

Date: 2026-09-08. These are collision criteria and excluded families,
not a resolution of Gottschalk surjunctivity. All arguments below are
algebraic; no computation was run.

Let G be a group and let T be a finite collection of elements of order
three whose cyclic subgroups are pairwise distinct. For each coset
e=g<t>, let p_e(x) be one on a nonconstant binary pattern and zero
on a constant pattern. Thus, writing the three bits as x_0,x_1,x_2,

    p_e(x)=x_0+x_1+x_2+x_0 x_1+x_0 x_2+x_1 x_2.

The parallel cellular automaton is

    F(x)=x+sum_(t in T) p_t(x),

where p_t(x) takes the constant value p_e(x) on e. One correction
gives the reversible nonconstant-triple complementation involution.
Repeated cyclic subgroups cancel in pairs, so T records the subgroups
that occur with odd multiplicity.

## Exact finite-difference criterion

Fix a finite nonempty set Delta in G. Call a coset cut if it meets
Delta in one or two points. Let E_Delta be the finite set of cut
cosets belonging to the selected cyclic subgroups. Each cut coset
has a unique pair of sites with the same Delta-membership status:
the two sites outside Delta in the one-point case, and the two
sites inside Delta in the two-point case. Make these pairs the
edges of a finite graph Gamma_Delta.

For a cut coset e, denote its pair by {u_e,v_e}. Direct expansion
of the quadratic polynomial gives

    p_e(x+1_Delta)+p_e(x)=1+x(u_e)+x(v_e).             (1)

For a coset meeting Delta in zero or three points, the difference
is zero. The three-point assertion also follows from invariance
of p_e under complementing all three bits.

For a function c:E_Delta -> F_2, define its incidence sum by

    Bc=sum_(e in E_Delta) c(e) 1_e.

There are finite configurations x and x+1_Delta with the same
F-image if and only if there exists c such that

    Bc=1_Delta,                                      (2)

and, on every cycle C of Gamma_Delta,

    sum_(e in C) c(e)=length(C) mod 2.                (3)

Indeed, (2) is exactly the vanishing output difference once c is
the correction difference. By (1), realizing that c amounts to
solving

    x(u_e)+x(v_e)=1+c(e).

This finite graph system is soluble exactly when its labels sum
to zero around every cycle, which is (3). Choose one root value
per connected component and extend along paths. Setting x to
zero off this graph supplies finite configurations. This proves
both directions and does not assume that G is finite or amenable.

## The four-bit construction has only one obstruction

Choose a,b in T and put

    A=<a> minus {1},     D=<b> minus {1},
    Delta=A union D={a,a^2,b,b^2}.

The two cyclic subgroups intersect only in 1. The canonical
solution of (2) selects just their identity cosets:

    c(<a>)=c(<b>)=1,     c(e)=0 otherwise.

Its incidence sum is 1_Delta because the common identity cancels.

The graph Gamma_Delta splits into vertices inside Delta and
vertices outside Delta. The inside graph never obstructs this
canonical selection. Its special edges are {a,a^2} and {b,b^2},
with required background difference zero. Every other inside
edge joins A to D, with required difference one: a different
C3 coset cannot contain both a and a^2, or both b and b^2.
Assigning x=0 on A and x=1 on D therefore solves every inside
constraint at once.

On the outside graph, every required difference is one. Thus:

**The canonical four-bit collision exists if and only if the
outside completion graph is bipartite.**

Here an outside completion edge joins the other two points of
any selected C3 coset meeting Delta exactly once. This criterion
allows coincidences among addresses; distinct-endpoint arguments
are sufficient but unnecessary.

An odd cycle rejects this particular coset selection. It does not
reject other solutions c of (2), other difference sets, or prove
that F is injective.

## Whole families decided by the criterion

### Exactly two distinct cyclic subgroups always collide

If T={a,b}, the outside completion edges from each subgroup form
a matching, because its cosets are disjoint. The union of two
matchings is bipartite. Consequently the parallel sum of these
two involutions is noninjective in every group.

One may take both background values on Delta to be zero in this
two-subgroup case. There are at most four outside edges, and a
smaller bipartition class in each component has at most four
vertices in total. Thus a collision can be chosen with

    |supp x| <= 4,     |supp(x+1_Delta)| <= 8.

### A commuting pair survives every extra correction when there are no involutions

Suppose a and b commute and G has no element of order two. Then
H=<a,b> is C3 x C3. Any collection T containing these subgroups
has the canonical four-bit collision, regardless of its other
order-three actors.

To prove bipartiteness, suppose an outside completion graph had
an odd cycle with successive vertices v_i. Write r_i in Delta
for the third point of its i-th C3 coset. The coset relation gives

    v_(i+1)=r_i v_i^(-1) r_i.

For an odd cycle length m, iterating this identity gives

    v_0=A v_0^(-1) B,
    A=r_(m-1) r_(m-2)^(-1) r_(m-3) ... r_1^(-1) r_0,
    B=r_0 r_1^(-1) ... r_(m-3) r_(m-2)^(-1) r_(m-1).

Only the r_i are commuted: they all lie in the abelian subgroup
H, so A=B. No commutation of v_0 with H is assumed. Therefore

    (v_0 A^(-1))^2=1.

The absence of involutions forces v_0=A in H. Every other cycle
vertex then belongs to H as well. But inside H, write a,b as an
additive basis. Outside Delta, the identity is isolated and the
only possible completion edges join the four corners +/-a +/-b
along the four sides of a square. To see this directly, a line
through a point of Delta either contains another Delta point,
or joins the two corners obtained by varying the other basis
coordinate. This graph has no odd cycle, a contradiction.

In particular, **every parallel family containing at least two
distinct C3 subgroups in any elementary abelian 3-group is
noninjective**. This includes all the subgroups simultaneously
in C3^n for every n>=2; adding more affine directions cannot
repair the collision.

### A common C3 quotient gives another sufficient condition

Suppose a homomorphism chi:G -> C3 is nontrivial on every selected
cyclic subgroup. Choose any two of them for Delta. All points of
Delta have nonzero chi-value. Every selected C3 coset has one
point in each of the three chi-fibers. An outside completion edge
therefore joins chi-value zero to nonzero chi-value. This is a
bipartition, so the canonical collision exists whenever |T|>=2.

## Extra actors can create a genuine odd-cycle obstruction

The outside-bipartiteness condition is not automatic in general,
even if the two selected actors commute. The following explicit
example has order 36 and involves five distinct C3 subgroups.

Let V=F_2^2, choose e nonzero, and let R have order three on V,
so that e+Re+R^2e=0. Work in

    G=(V semidirect_R C3) x C3 = A4 x C3,

using coordinates (v,k,z), with k,z modulo three, and product

    (v,k,z)(w,l,t)=(v+R^k w,k+l,z+t).

Use the actors

    g=(0,1,0),
    h=(R^2e,1,2),
    kappa=gh=(e,2,2),
    a=(e,1,1),
    b=(0,0,2).

They all have order three. Their cyclic subgroups are distinct,
as is checked by their listed representatives and squares:

    g^2=(0,2,0),
    h^2=(Re,2,1),
    kappa^2=(Re,1,1),
    a^2=(R^2e,2,2),
    b^2=(0,0,1).

The selected pair a,b commutes because b is central. Set
Delta={a,a^2,b,b^2}, and consider three points outside Delta:

    u=(e,2,1),     v=(e,0,1),     w=(Re,1,0).

Literal multiplication gives

    u g=v,           u g^2=a,
    v h=w,           v h^2=a^2,
    u kappa=w,       u kappa^2=b.

Hence the outside completion graph contains the triangle

    {u,v} from u<g>,
    {v,w} from v<h>,
    {u,w} from u<kappa>.

All three edges require background difference one under the
canonical two-coset selection, which is inconsistent. This
explains exactly why the no-involutions proof cannot be extended
to every ambient group: the closing square equation can retain
a nontrivial involution.

This example proves failure of the canonical construction. It
does not assert injectivity of this five-actor automaton. Whether
every parallel family with at least two distinct C3 subgroups is
noninjective remains undecided by these arguments; the full
criterion (2)-(3) is the appropriate next test.

Related exact atlas collisions are recorded in
`research/artifacts/gottschalk-parallel-order-three-five-point-collision-2026-09-08.md`.
