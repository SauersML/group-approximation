# Rigidity of linear and affine directed quadratic intertwiners

Date: 2026-09-08. Let the source permutation T have no cycles of
length one or two. Every nonzero row of a continuous linear map
intertwining Q(x)=xTx copies one source coordinate, and its next
target row copies that coordinate's successor. Every bijective
continuous affine intertwiner is a coordinate permutation
conjugating the directed source and target permutations.

For finite target cycles, the full nonbijective classification is
oriented source-cycle copies and constant target cycles. In
particular, for products of three-cycles, these are oriented copies
of source triples and constant 000 or 111 target triples; a linear
intertwiner only permits the constant 000. Infinite target orbits
require a weaker, forward-closed statement specified below.

This rules out a direct scalar encoding of the reversible two-track
triangular feedback by a Q-intertwining linear or affine change of
coordinates. It also rules out injective encodings of this kind
into a code invariant under a transitive target coordinate action.
The result does not exclude nonlinear encodings, changes that fail
to intertwine Q, or encodings into non-invariant codes. It is a
structural restriction on this route, not a resolution of Gottschalk's
conjecture. The index sets below may be infinite; no computation or
measure-preservation argument is used.

For context, Phung's
[geometric direct-finiteness paper](https://arxiv.org/abs/2111.07930)
proves direct finiteness for the polynomial near ring on sofic
groups (Theorem A) and stable finiteness of group algebras on
surjunctive groups (Theorem B). Those hypotheses do not supply
a conclusion for an arbitrary group here. The present argument
classifies a restricted family of intertwiners; it does not
prove direct finiteness of the whole polynomial near ring.

## Linear row theorem for arbitrary index sets

Let I and J be sets, with permutations tau on I and sigma on J
such that tau has no cycles of length one or two. There is no
restriction on sigma, and infinite source or target orbits are
allowed. Give the configuration spaces their product topologies
and define

    Q_tau(x)(i)=x(i)x(tau(i)),
    Q_sigma(y)(j)=y(j)y(sigma(j)).

Suppose L:F_2^I -> F_2^J is continuous and F_2-linear, and

    Q_sigma L=L Q_tau.                              (1)

Then the set J_+ of nonzero target rows is forward-closed under
sigma, and there is a map gamma:J_+ -> I such that

    (Lx)(j)=x(gamma(j))       for j in J_+,
    (Lx)(j)=0                for j outside J_+,
    gamma(sigma(j))=tau(gamma(j)).                   (2)

Thus every nonzero row selects one coordinate. If a target orbit
has finite period m and contains a nonzero row, the whole orbit
copies a source cycle whose period divides m. On an infinite
target orbit, zero rows may precede an infinite forward run of
copied coordinates; they need not form a union of whole orbits.
Conversely, every map described in (2) intertwines Q, by direct
evaluation at each target coordinate.

## Proof by squarefree monomials

Continuity makes every output row of L a finitely supported linear
functional. Fix a target coordinate j, and let ell be its row and
eta the row at sigma(j). Equation (1) says

    ell(Q_tau x)=ell(x)eta(x)                        (3)

for every x. Suppose ell is nonzero, and let S and H be the finite
supports of ell and eta. Since tau has no fixed points, Q_tau
vanishes on every source unit vector. Evaluating (3) there gives
S intersect H empty.

The left side of (3) is the sum of the squarefree monomials

    x_i x_(tau(i)),       i in S.

These monomials are all distinct: two different directed edges
would give the same unordered pair only on a two-cycle, which is
excluded. No such edge can have both endpoints in S, since the
right side contains only monomials between S and H. Thus no
member of S has its successor in S.

Fix i in S. Exactly one left-side monomial is incident to i,
namely x_i x_(tau(i)). An incoming edge from another member of
S is impossible by the preceding observation. On the right,
the monomials incident to i are exactly x_i x_h for h in H,
without cancellation because S and H are disjoint. Equality
therefore forces

    H={tau(i)}       for every i in S.

Since tau is injective, S is a singleton. Thus ell copies one
coordinate i, and eta copies tau(i). Applying this at each
nonzero target row proves (2), including forward closure. Only
finitely many variables occur in (3), so the uniqueness of the
squarefree polynomial representation is being used in a finite
Boolean cube, even when I and J are infinite.

The infinite-target qualification is real. Let the source be one
three-cycle and let the target be Z with sigma(n)=n+1. The linear
map that outputs zero for n<0 and x_(n mod 3) for n>=0 intertwines
Q. Its nonzero rows occupy a proper forward ray of one target
orbit.

The exclusion of source two-cycles matters as well. On a two-site
swap, Q(x_0,x_1)=(x_0x_1,x_0x_1), and the linear map
L(x_0,x_1)=(x_0+x_1,0) satisfies QL=LQ=0. Its nonzero row does
not copy one coordinate. If the source and target permutations
are identity, Q is identity and every linear map intertwines it.

## Affine maps and finite target cycles

Suppose instead L(x)=L_0x+c is continuous and affine, with L_0
linear, and still satisfies (1). Evaluating at zero gives

    Q_sigma(c)=c.

Thus c_j=1 implies c_(sigma(j))=1. For every source unit vector
e_i, Q_tau(e_i)=0, so

    Q_sigma(L e_i)=L(0)=c.

At any target coordinate j with c_j=1, the product defining
Q_sigma(L e_i)(j)=1 forces (L e_i)(j)=1=c_j. Every coefficient
of the jth row of L_0 is consequently zero, and continuity makes
that row zero. Hence every coordinate where c=1 is a constant
output coordinate of L.

For a row j with c_j=0, there are two cases. If c_(sigma(j))=1,
the next row of L is the constant one. The intertwining equation
at j is then ell(Q_tau x)=ell(x). Source unit vectors force every
coefficient of ell to vanish, making this row constant zero. If
c_(sigma(j))=0, the equation is precisely (3), so the linear row
proof applies. Consequently every affine target row is constant
zero, constant one, or one selected source coordinate. Copied rows
advance to the corresponding successor copy, and constant-one
rows advance to constant-one rows. These are row-wise statements;
on an infinite orbit a zero row can precede either kind.

If every target orbit is finite, c is constant on each orbit.
The orbits with c=1 are constant-one outputs. On orbits where
c=0, the linear row theorem applies without change. Therefore
each finite target cycle is constant zero, constant one, or an
oriented copy of a source cycle whose period divides the target
period. When both permutations consist of three-cycles, this is
exactly the asserted copy/000/111 classification.

Thus we do not assert a constant-or-copy decomposition into whole
orbits for nonbijective maps with infinite target orbits: even c
itself may be a zero-to-one step sequence along such an orbit.

## Bijective and scalar equivariant consequences

For a linear L, injectivity requires every source coordinate to
be copied, and surjectivity requires no zero rows and no duplicate
copies. Hence a linear bijection is exactly a coordinate permutation
gamma:J -> I satisfying gamma sigma=tau gamma.

For an affine surjection, the preceding argument rules out any
c_j=1, since that would make a target coordinate constant. Thus
c=0 and the linear theorem applies. Consequently every bijective
continuous affine intertwiner is the same kind of coordinate
permutation. This bijective conclusion holds even when the target
has infinite orbits.

There is a particularly strict scalar consequence. Let G be a
group, let t have order at least three or infinite order, and let
s be any element. Use R_h x(g)=x(gh). Every
nonzero continuous linear G-equivariant map L:F_2^G -> F_2^G
satisfying

    Q_s L=L Q_t

has the form

    L=R_h,       s=h t h^-1.                         (4)

Indeed equivariance makes the selected coordinate in the row at
g equal to gh for a fixed h. Intertwining then gives sh=ht.
When s=t, h must centralize t. The zero operator is the only
other linear intertwiner. The complete affine list consists of
the same shifts and the constant maps to 0 and 1.

Thus even allowing noninvertible continuous linear intertwiners
does not permit matrix combinations of coordinates: the condition
of preserving Q already restricts them to copies and zeros.

## Obstruction to scalarizing the two-track triangular control

Take any group G, t of order three, and h in G. On two independent
tracks define

    F_tri(x,y)=(x+R_h Q_t(y),y).                     (5)

This is a reversible involution. Its globally fixed output
coordinates are exactly those on the second track: every y
coordinate is unchanged for all inputs, whereas taking y=1
changes every x coordinate. This is a nonempty proper subset of
the source coordinate set.

Any group of coordinate permutations commuting with a map
preserves its globally fixed-coordinate set. Therefore no
transitive coordinate-permutation group can commute with (5),
or with any coordinate relabelling of it. Since a bijective
continuous linear or affine Q-intertwiner is only such a
relabelling, it cannot conjugate (5) into a scalar cellular
automaton for a transitive target coordinate action.

This is relevant in particular when h does not normalize <t>:
the two-track control then has bijective compressed B and nonzero
off-axis K, as shown in
[the unrestricted-feedback artifact](gottschalk-unrestricted-order-three-odd-parity-obstructions-2026-09-08.md).
The obstruction here explains why its direct Q-preserving linear
scalarization cannot supply a scalar example.

## The same obstruction for invariant linear or affine codes

More generally, suppose L is an injective continuous linear or
affine Q-intertwiner from the two-track space into a scalar target
configuration space. Write C=im L. Suppose a group Lambda acts
transitively on target coordinates, preserves C, and a target map
F' is Lambda-equivariant with

    F' L=L F_tri.                                   (6)

The classification shows that target coordinates are constants or
copies of source coordinates. Injectivity ensures that coordinates
from both source tracks are copied somewhere. On C, every constant
coordinate and every copied y coordinate is fixed by F'. No
copied x coordinate is fixed for all points of C, since y=1 in
(5) changes it. Thus the coordinates fixed by F' on every point
of C again form a nonempty proper subset.

Because Lambda preserves C and commutes with F', this subset is
Lambda-invariant, contradicting transitivity. Hence no encoding
satisfying all these hypotheses exists. The code-invariance
assumption is explicit and necessary for this argument; the
conclusion does not extend here to non-invariant codes, nonlinear
encodings, or linear changes that do not intertwine Q.

## Commuting order-three feedback must be trivial

Return to a product of three-cycles and its map Q(x)=xTx.
Let A be any continuous linear endomorphism of the configuration
space. Neither equivariance nor injectivity is needed for the
following assertion:

    F=x+A Q and FQ=QF imply A=0.                    (7)

Fix a source unit configuration q. Then Qq=0, and q belongs to
the image of Q: its active triple has a unique weight-two
preimage. The fiber Q^-1(q) is the product of this singleton
triple with

    S_0={000,100,010,001}

on every other triple. For x in this fiber, F(x)=x+Aq. Commutation
gives Q(F(x))=F(Qx)=F(q)=q, so translation by Aq maps the entire
fiber into itself.

Every factor of this product has trivial translation stabilizer.
This is immediate for the singleton factor. For S_0, an inclusion
S_0+v contained in S_0 forces v in S_0; if v is a nonzero unit
vector, adding a different unit vector produces a weight-two
state outside S_0. Thus v=0. Projecting the fiber inclusion onto
each triple therefore gives Aq=0. This holds for every source
unit q, so A vanishes on finitely supported configurations and,
by continuity and density, on the entire space. This proves (7).

In particular, a nonidentity scalar rule in the feedback family
x+A Q_t cannot itself be a Q_t-centralizer. This conclusion does
not extend to arbitrary nonlinear maps, as the following control
shows.

## A nonlinear scalar centralizer outside the feedback family

Let G=C_3 x C_2, with t generating C_3 and s generating C_2.
Write T=R_t and define the indicator of an all-one triple by

    M(x)=x(Tx)(T^2x),       m(x)=R_s M(x).

The mask m is constant on each t-triple and records whether the
other triple is 111. Define the scalar G-equivariant local map

    H(x)=(1+m(x))x+m(x)Tx.                           (8)

It rotates a triple precisely when the other triple is 111.
Every selected rotation preserves each triple's M value, so
M(Hx)=M(x) and m(Hx)=m(x). Consequently H is reversible, with

    H^-1(x)=(1+m(x))x+m(x)T^2x.

Also M(Qx)=M(x), because the product of the three adjacent-pair
products is the original triple product over Boolean inputs.
Thus m(Qx)=m(x). Since a rotation selected by a t-invariant mask
commutes with the adjacent-pair operation,

    Q(Hx)=(1+m(x))Qx+m(x)TQx=H(Qx).

The map is nonlinear. Let p be a unit vector in the first triple
and z be 111 on the other triple and zero on the first. Then
H(p)=p and H(z)=z, but H(p+z)=Tp+z, which differs from p+z.
Since H(0)=0, it is not affine either. Thus nonlinear
scalar reversible Q-centralizers exist. By (7), this H cannot
be written x+A Q for any continuous linear A.
