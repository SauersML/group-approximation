# Directed quadratic intertwiners and a nonlinear scalarization obstruction

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

The affine classification excludes scalarizing the displayed
triangular control into any equivariant target map, including
through invariant codes, without target injectivity or zero
preservation. An independent obstruction allows more general
encodings: it rules out encoding the
displayed reversible two-track triangular feedback into any
injective zero-preserving scalar binary cellular automaton by
even a nonlinear Q-intertwining bijection. It also excludes
Q-intertwining injections into invariant codes. A second intrinsic
stratum excludes full Q-preserving conjugacies for balanced
triangular feedback with nonzero action on im E; its invariant-code
extension is not proved here. The first proof uses a point uniquely
characterized by Q, and needs neither continuity nor finiteness.
Encodings that do not intertwine Q and encodings
into non-invariant codes remain outside that conclusion. Other
nonlinear Q-intertwiners can exist, as an explicit control below
shows. These are structural restrictions on this route, not a
resolution of Gottschalk's conjecture. No computation or
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

## Affine invariant-code obstruction with arbitrary equivariant targets

For the two-track triangular rule

    F_tri(x,y)=(x+R_h Q_t(y),y),

let L be a continuous affine injective intertwiner from the
source product of three-cycles to a scalar target product of
three-cycles. Suppose its image C is invariant under a group
Lambda acting transitively on target coordinates. There is no
Lambda-equivariant target map F' satisfying F'L=L F_tri.
No injectivity, continuity, or zero-preservation assumption on
F' is needed for this assertion.

Indeed every row of L is a source-coordinate copy or a constant,
and injectivity requires every source coordinate to be copied
somewhere. Let J_fix consist of target coordinates j for which
F'(z)(j)=z(j) for every z in C. Constant rows and copies of y
coordinates belong to J_fix, whereas copies of x coordinates
do not: the corresponding coordinate of R_h Q_t(y) can be one.
Thus J_fix is nonempty and proper. Equivariance of F' and
invariance of C make J_fix invariant under Lambda, contradicting
transitivity. This proves both the full-conjugacy and invariant-code
obstructions for affine encodings. Unlike the nonlinear code
argument below, this proof does not require the target action
to commute with Q.

## A point distinguished by the order-three quadratic map

On any product of three-cycles, the all-one configuration is the
unique fixed point of Q whose Q-preimage is a singleton. Indeed,
a fixed triple is either 000 or 111. If a fixed configuration
has a 000 triple, varying that triple over
{000,100,010,001} gives at least four preimages, while leaving
all other triples unchanged. The all-one configuration has only
itself as a preimage.

This characterization works for infinite products as well. Any
bijective Q-intertwiner sends fixed points to fixed points and
induces bijections of their preimage fibers. It must therefore
send the all-one source configuration to the all-one target
configuration, regardless of linearity or continuity.

## Nonlinear obstruction to scalarizing the triangular control

Take any group G, t of order three, and h in G. On two independent
tracks define

    F_tri(x,y)=(x+R_h Q_t(y),y).                     (5)

This reversible involution moves the all-one configuration:

    F_tri(1,1)=(0,1) != (1,1).

By contrast, every injective zero-preserving scalar binary
cellular automaton F' fixes the all-one configuration. More
generally this holds for an injective zero-preserving map
equivariant under any transitive coordinate action. Equivariance
maps a constant input to a constant output, so F'(1) is 0 or 1;
injectivity and F'(0)=0 exclude the first choice.

Suppose L is any bijection intertwining the source and target
order-three quadratic maps and satisfying

    F' L=L F_tri.

The preceding characterization gives L(1,1)=1. Evaluating this
identity there makes its left side 1, but its right side differs
from 1 because F_tri(1,1) differs from (1,1) and L is injective.
This is a contradiction. Thus no such Q-preserving conjugacy
exists, even if L is nonlinear and discontinuous. The target
F' need not belong to the particular family x+A Q.

This is relevant in particular when h does not normalize <t>:
the two-track control then has bijective compressed B and nonzero
off-axis K, as shown in
[the unrestricted-feedback artifact](gottschalk-unrestricted-order-three-odd-parity-obstructions-2026-09-08.md).
The obstruction here explains why its direct Q-preserving
scalarization cannot supply a scalar example, even through a
nonlinear change of coordinates.

## The same obstruction for nonlinear invariant-code encodings

More generally, let L be any injective Q-intertwiner from the
two-track space into a scalar binary target configuration space,
and write C=im L. Suppose a group Lambda acts transitively on
target coordinates, preserves C, and commutes with the target
Q. Suppose also that F' is injective, zero-preserving and
Lambda-equivariant, with

    F' L=L F_tri.                                   (6)

The map L is a bijection from the source onto C, and intertwining
makes Q restricted to C conjugate to the source quadratic map.
Consequently p=L(1,1) is its unique fixed point with a singleton
preimage fiber, where the fiber is taken inside C.

Since Lambda preserves C and commutes with Q, its action preserves
this unique characterization and fixes p. Transitivity on the
binary target coordinates makes p a constant configuration,
either 0 or 1. The preceding argument shows that F' fixes both
constants, so F'(p)=p. But (6) gives

    F'(p)=L F_tri(1,1) != L(1,1)=p,

a contradiction. No linearity, affinity, continuity, or finite
cardinality of the configuration spaces is used. Code invariance
and commutation of the target action with Q are explicit
hypotheses; they hold for a scalar cellular automaton's shift
action and an invariant code. Non-Q-preserving encodings and
encodings into non-invariant codes are not excluded here.

## Balanced triangular feedback and the one-defect stratum

The all-one argument has a specific hypothesis: the displayed
triangular control (5) moves that configuration. A balanced
triangular involution instead has the form

    F_A(x,y)=(x+A Q_t(y),y),       A1=0,

where A is a continuous linear cellular automaton. It fixes the
all-one configuration. For example A=I+R_h gives such a map.
A different invariant excludes its full Q-preserving
scalarization whenever

    AE != 0,       E=I+T+T^2.                       (7)

Among fixed points of Q on products of three-cycles, those with
exactly four preimages are precisely the all-one configurations
with a single zero triple. Call this the one-defect stratum.
There is one such point per triple. A zero-free fixed point has
one preimage; one zero triple gives four; two or more zero triples
give at least sixteen by varying two factors. This proves the
characterization also for infinite products.

Every bijective Q-intertwiner maps this stratum bijectively onto
the target's one-defect stratum. For a scalar group shift, the
group acts transitively on the stratum, since it acts transitively
on the right-t orbits. Hence an equivariant target map either
fixes every point of the stratum or fixes none: its fixed-point
subset is invariant under that transitive action.

The source F_A has a proper nonempty fixed-point subset there.
It fixes every one-defect state whose zero triple is in the x
track, because y=1 and A1=0. Condition (7) supplies a block
indicator e_i with A e_i nonzero: these indicators span a dense
subspace of im E, and A is continuous. At the state with the
zero triple in that y block, the update of x is

    A(1+e_i)=A e_i != 0.

So some y-track defect is moved. A Q-preserving conjugacy would
transport this proper nonempty fixed subset to the scalar target's
transitive stratum, a contradiction. Thus no such full conjugacy
exists. This argument does not require zero preservation of the
target map; equivariance suffices for the fixed-subset contradiction.

In particular, A=I+R_h with h not normalizing <t> has nonzero
(I-E)AE and therefore AE nonzero, so it is covered. Together
with the all-one argument, this excludes full Q-preserving
scalarizations of the balanced outside-axis controls and the
displayed unbalanced control (5).

The balanced argument does not yet extend to arbitrary invariant
codes. Four preimages inside a code need not mean four ambient
preimages, and the resulting intrinsic stratum inside the code
need not be a transitive target-group orbit. Thus the invariant-code
obstruction proved above applies to the unbalanced control (5);
no corresponding balanced-code conclusion is asserted here.

A separate [finite-source invariant-code theorem](gottschalk-balanced-invariant-code-finite-exclusion-and-infinite-prefix-control-2026-09-08.md)
now excludes balanced codes whenever the source group is finite
and A is nonzero. Its three distinguished points use Q^2-fiber
sizes. That artifact also gives an infinite prefix homeomorphism
showing why the same distinguished-point argument does not extend
unchanged. An [infinite scalar-code construction](gottschalk-balanced-triangular-invariant-scalar-code-construction-2026-09-08.md)
now gives a continuous Q-preserving encoding with reversible
dynamics on a proper invariant code. An injective or reversible
extension to the entire scalar full shift remains unresolved.

## Commuting order-three feedback must be trivial

Return to a product of three-cycles and its map Q(x)=xTx.
Let A be any continuous linear endomorphism of the configuration
space. Neither equivariance nor injectivity is needed for the
following assertion:

    F=x+A Q and FQ=QF imply A=0.                    (8)

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
by continuity and density, on the entire space. This proves (8).

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

    H(x)=(1+m(x))x+m(x)Tx.                           (9)

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
scalar reversible Q-centralizers exist. By (8), this H cannot
be written x+A Q for any continuous linear A.
