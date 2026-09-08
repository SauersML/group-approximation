# Quadratic elimination when the other operand is outside the guard

Date: 2026-09-08. This is a positive exclusion for a construction class,
not a proof of Gottschalk's conjecture. No computation was used.

## Statement

Let k be a finite field, G any group, and H any subgroup. Consider

    F(x)(g)=x(g)+sum_i lambda_i x(gh_i)x(gs_i),
    h_i in H,   s_i outside H,                            (1)

with finitely many nonzero coefficients and addresses. If F is
injective, then F is surjective. No surjunctivity, amenability,
commensuration, or finiteness assumption is made on H.

More generally, the same assertion applies whenever H contains
exactly one operand of every quadratic monomial. The two factors may
be reordered to give (1).

The proof extends target-multiplicative block elimination to finitely
many colored cosets. The main issue is uniform locality of the
intermediate inverses, since individual coset restrictions need not
be cellular automata over H. We obtain this locality on a compact
G-invariant coefficient space, keeping every coloring fixed during
all finite modifications.

## A colored block lemma

Let C be any compact G-invariant space of color configurations with
finitely many labels 0,1,...,m. Extra finite local coefficient symbols
may be included in C. Data take values in k, and are required to be
zero at sites of color 0. Write Z_C for the resulting compact
G-invariant space of pairs (c,x).

Suppose a local G-equivariant map P on Z_C preserves c and has the
following form. Its output is zero at color 0. At an output site of
color i>0, it is x(g) plus a finite sum of bilinear terms, each having
one operand of color i and one operand of a different color. An operand
at color 0 makes its term zero. Coefficients and the choice of terms
may depend locally on c. Then injectivity of P implies bijectivity.

For fixed c, let X_i denote all data coordinates of color i. The rule
has the target-multiplicative form

    P_i=X_i+sum_(j distinct from i) B_(i,j)^c(X_i,X_j).    (2)

The blocks may be infinite and spatially nonperiodic. The proof below
does not assume their individual restrictions are equivariant over
some subgroup.

## Induction and the zero-block restriction

Induct on the number of active data colors. Colors that are removed
remain unchanged in c; their data are simply fixed to zero. Thus every
inductive domain is still compact and G-invariant. Since each output
term contains an operand in its own color block, setting a whole block
to zero makes its whole output block zero. The zero-block restriction
is consequently a self-map of the smaller domain and inherits
injectivity.

With at most one active color, all nonlinear terms vanish and P is
identity. For the inductive step, put X=X_1 and let Y collect the other
active blocks. Write

    P_c(X,Y)=(L_(c,Y)X,V_c(X,Y)),
    v_(c,0)(Y)=V_c(0,Y).

The induction hypothesis makes the family of zero-X restrictions
v_(c,0) bijective. This family is a homeomorphism on its compact
invariant domain and commutes with G. Its inverse therefore has
uniform finite memory, by the argument given below for every inverse
introduced in the proof.

For each c,Y, the map L_(c,Y) is homogeneous linear. If L_(c,Y)X=0,
choose Y' with v_(c,0)(Y')=V_c(X,Y). Then

    P_c(X,Y)=P_c(0,Y').

Injectivity gives X=0. Thus all these linear maps are injective, and
the local equivariant map

    E(c,X,Y)=(c,L_(c,Y)X,Y)                               (3)

is injective on the entire compact colored domain.

## Bijectivity and locality of the linearizing map

Fix c and a finitely supported Y. Every nonlinear term in the first
output block contains a Y operand. Locality therefore implies that
L_(c,Y) differs from identity at only finitely many output coordinates.
An injective self-map with this property is bijective: for each fixed
configuration outside the affected finite set, it is an injective
self-map of the finite set of possible fillings inside that set.

Consequently the image of E contains every point with finitely
supported Y, arbitrary X, and arbitrary fixed c. These points are
dense in the colored domain. The image of E is compact and hence
closed, so E is surjective and therefore a homeomorphism.

Here is the uniform locality assertion used at every inductive stage.
A continuous equivariant inverse on a compact invariant subshift has
a finite determining set for its output coordinate at 1: continuity
into the finite alphabet gives cylinder neighborhoods, and compactness
reduces them to a finite cover. Equivariance translates that same
finite set D to every gD. This applies to E^-1 and to every previously
proved bijective zero-block family. If the coloring is fixed and data
change only on a finite set S, inverse outputs can change only in
S D^-1, which is finite. No inverse is assumed local before its
bijection and compactness have been established.

## Eliminating the remaining output block

Set D_c=P_c E_c^-1. This family is local, equivariant, and injective,
and it preserves X. Its zero-X fiber is v_(c,0): injectivity of
L_(c,Y) gives E_c^-1(0,Y)=(0,Y).

For fixed c and finitely supported X, the map on the Y fiber differs
from v_(c,0) at only finitely many output coordinates. Indeed, compare
the data (X,Y) and (0,Y), using the uniform finite memory of D; this
finite affected set is independent of Y. Composing the fiber map
with v_(c,0)^-1 gives an injective self-map fixing every coordinate
outside that finite set. Finite filling counts make it bijective.

Thus the image of the full family D contains all points with finite
X support and arbitrary Y, for each unchanged c. Density and compactness
make D surjective. Therefore P=D E is bijective, completing the
induction. All inverses needed by later induction steps are again
uniformly local by the compact equivariant argument above.

Only data coordinates were changed in the density and finite filling
arguments. They always respect the existing color masks. No finite
modification of a constrained coloring was used.

## The compact space of colored H-cosets

Fix m and let C_m consist of colorings c:G -> {0,1,...,m} satisfying

1. c(gh)=c(g) for every h in H;
2. each nonzero color occurs on at most one coset gH.

These conditions are closed: each violation is visible on finitely
many specified coordinates. They are also preserved by left G
translation. Hence C_m is compact and G-invariant. Its colorings
include every assignment of distinct nonzero labels to at most m
cosets, with color 0 outside their union. A nonempty positive color
class is exactly one H-coset; labels are allowed to be absent.

Use the domain Z_(C_m) of data that vanish at color 0. For (1), a
guard address h_i in H always has the same color as the output site.
If that output color is nonzero, the address s_i outside H lies in
a different H-coset. Its color is therefore different, or zero.
If the output color is zero, its linear term and all guard operands
are zero. Thus

    (c,x) -> (c,F(x))

is a self-map of this compact colored domain and satisfies the block
lemma. It is injective because F is injective on the original full
shift. The lemma makes it bijective, and preservation of c makes its
restriction to each fixed colored union of H-cosets bijective.

Every finitely supported target is contained in a finite union V of
H-cosets. Color those cosets separately and apply the preceding
bijection to obtain a preimage supported in V. All finitely supported
targets are therefore attained. The image of F is compact, so density
proves surjectivity on k^G. This proves (1).

## Consequence for the common-right-factor family

For

    F(x)=x+(R_r x)(R_(rt) x)+(R_s x)(R_(st) x),           (4)

write M=<r,s,t>. The four possible subgroups generated by one operand
from each pair are

    <r,s>,   <r,st>,   <rt,s>,   <rt,st>.

If any one of these subgroups H is proper in M, it contains exactly
one operand from each pair. Indeed, containing any third operand
recovers t by division within a completed pair, and then recovers the
remaining operand; it would therefore give H=M. The theorem excludes
an injective nonsurjective rule whenever any of these four subgroups
is proper, regardless of whether its surjunctivity is known.

Consequently a strict candidate within (4) must have all four displayed
subgroups equal M. This is an additional necessary condition, not an
injectivity certificate or an assertion that such a nonsurjunctive
memory group has been constructed. A known surjunctive guard also
excludes a candidate by the separate surjunctive-guard transfer theorem.
