# Every surjunctive guard subgroup suffices

Date: 2026-09-08. This removes the virtually polycyclic restriction
from the preceding guard theorem. The proof uses a finite poset of
subgroup intersections, rather than a numerical rank. It does not
prove that arbitrary groups are surjunctive. No computation was run.

## Statement and its scope

Let A be a finite nonempty alphabet with distinguished symbol 0,
let H be a surjunctive subgroup of an arbitrary group G, and let
F:A^G -> A^G be an injective cellular automaton. Suppose F preserves
configurations supported in every union of cosets gH. Then F is
surjective.

The support condition means that F(x)(g)=0 whenever x vanishes on
gH. For a finite-field polynomial rule without a constant term, it
holds if every monomial has an operand whose address belongs to H.
Neither commensuration nor amenability of H is required.

The hypothesis that H is surjunctive is essential to what is proved:
taking H=G makes the support condition automatic for every CA fixing
zero. A CA always sends constant configurations to constants; for
an injective CA, composing with a symbol permutation makes one such
constant fixed. Thus proving this statement for arbitrary H without
its surjunctivity hypothesis would already prove Gottschalk.

## A finite poset replaces subgroup rank

For subgroups B,C of G, write

    B <=_a C  if  [B:B intersect C] is finite.

This is a preorder. For transitivity, if B<=_a C and C<=_a D, then
B intersect C intersect D has finite index in B intersect C and
therefore in B. Mutual almost-inclusion is exactly commensurability.
Consequently the commensurability classes carry a partial order.

Given finitely many subgroups K_1,...,K_n, form the finite collection

    I={intersection_(i in J) K_i : empty != J subset {1,...,n}}.

There are at most 2^n-1 members. The empty intersection, which would
introduce the ambient group, is not included. The collection is
closed under nonempty intersections. Its commensurability classes
form a finite poset; fix a linear extension, numbered so that strict
almost-inclusion increases the number.

The coefficient operations in the proof below never leave I:
right translation of a coset preserves its left stabilizer,
intersection of cosets intersects their left stabilizers, and an
isolated inverse uses the intersection of its class's stabilizers.
No retained coefficient operation conjugates a stabilizer.

## Finite coset avoidance for arbitrary groups

A group cannot be covered by finitely many cosets of infinite-index
subgroups. This is the classical finite-coset-cover theorem of
[B. H. Neumann, Groups covered by finitely many cosets (1954)](https://publi.math.unideb.hu/paper/2620).
Here is a proof of precisely the version used.

Suppose a cover by n right cosets of infinite-index subgroups exists,
and induct on n. Among their stabilizers choose a maximal
almost-inclusion class. Let L be the intersection of the stabilizers
in that class. Each chosen-class coset is a finite union of right
L-cosets, and L has infinite index in the ambient group. Choose a
right L-coset disjoint from all these finitely many cosets.

Its intersections with the remaining covering cosets would cover it.
Each nonempty intersection is a right coset of L intersect K_i.
Every such intersection subgroup has infinite index in L: otherwise
the selected class would be almost-contained in the class of K_i,
contradicting maximality and the fact that K_i is outside that class.
Right translation identifies this with a cover of L by fewer than n
cosets of infinite-index subgroups, contradicting the induction
hypothesis. The case n=1 is immediate. Left-coset avoidance follows
by inversion.

## Finite coset-mask theorem

Consider a finite-memory map P:A^G -> A^G of the form

    P(x)(g)=f_(eta(g))((x(gs))_(s in M)),
    eta_i(g)=1_(K_i a_i)(g),
    f_0((z_s))=z_1,

where M is finite and contains 1. Assume that every K_i is
surjunctive and that P has a uniformly local inverse on its image:
some finite D containing 1 satisfies

    P(x)|_(gD)=P(y)|_(gD)  implies  x(g)=y(g)          (1)

for all g,x,y. Then P is bijective.

Surjunctivity passes to subgroups. Indeed, extend any injective CA
over a subgroup independently to all its left cosets in a surjunctive
group. This is an injective CA with the same finite memory over the
larger group, so it is onto, and its restriction to the original
coset is onto. Therefore every member of I above is surjunctive.
Conjugation also preserves surjunctivity.

Choose the class j with the largest number currently present among
the masks. Let L be the intersection of its present stabilizers and
let U be the union of its masks. The subgroup L has finite index in
each of those stabilizers, so U is a finite disjoint union of free
left L-orbits. Define P_j by keeping the class-j mask bits and setting
all the other bits to zero. It is L-equivariant and fixes G minus U.

The map P_j inherits (1). Given a finite output window W, left
translation by h in L preserves all class-j masks. A non-j mask at
a point w in W forbids h in a coset of L intersect K_i, when that
set is nonempty. This subgroup has infinite index in L: a finite
index would give class j <=_a class K_i, contrary to the choice of
j. The finite-coset avoidance result supplies h avoiding every
non-j mask throughout W. The translated rule of P is then exactly
the rule of P_j on W. All translates retain radius D in (1), so
using W=gD proves (1) for P_j. The temporary translated maps are
used only for this inference; their stabilizers are not retained.

On the zero-exterior fiber, P_j is an injective finite-track CA over
L: writing U as finitely many orbits L r_q turns every input address
h r_q s in U into h l r_p for a fixed l in L. Its alphabet is a
finite power of A. Surjunctivity of L makes this fiber map bijective.

For any finitely supported exterior input c, the fiber map differs
from the zero-exterior bijection in only finitely many output
coordinates. It is still injective by (1). Composing it with the
inverse of the zero-exterior map gives an injective map fixing the
complement of a finite set E. Every fixed exterior-of-E fiber is
the finite set A^E, so this map is bijective. Thus all finite-support
exterior fibers are onto. They are dense in the exterior full shift;
compactness of the image now makes P_j bijective on A^G.

Its inverse has finite memory by (1), is L-equivariant, and fixes
G minus U. It therefore has one local rule for each of the finitely
many orbits L r_q and the identity rule outside U. Its masks have
stabilizer L, which belongs to I and to class j.

Cancel this bijection on the input side:

    R=P composed with P_j^-1,
    W=union of the original non-j masks.

Outside W the local rules of P and P_j agree on every input, so R
is the identity there. Composition introduces the original masks
and right translates of the inverse masks L r_q. Their stabilizers
remain in I. Replace each class-j mask C in that description by
C intersect W. This retains its bit on W; outside W the rule is
already identity. Each replacement is a finite union of cosets of
intersections between a class-j stabilizer and a non-j stabilizer.
Every such intersection has a strictly lower class than j. Indeed,
it is contained in the class-j stabilizer, and equality of classes
would imply j<=_a K_i, which was excluded above.

The local recovery radius survives cancellation: recover the finitely
many coordinates of P_j^-1(x) needed by P_j using (1) for P, then
apply P_j. In particular R remains uniformly injective.

All retained stabilizers still belong to I. Class j has disappeared,
all new classes have smaller numbers, and all other present classes
already had smaller numbers. Induction on the largest present class
number therefore terminates at the empty-mask identity. Applying it
to R, and composing back with P_j, proves P bijective. This also
handles infinite minimal stabilizers: there is no finite-group base
case hidden in the induction.

## Applying the theorem to a guard

Let V be a finite union of cosets g_i H. Zero-fill an input outside
V to obtain z, and define

    P_V(x)(g)=F(z)(g) on V, and P_V(x)(g)=x(g) off V.

If S is the finite memory of F, masks g_i H and g_i H s^-1, s in S,
describe this map. Their left stabilizers are g_i H g_i^-1, which
are surjunctive. The map is identity when all mask bits vanish.

Injectivity, equivariance, and compactness give F a uniform local
inverse radius D on its image; enlarge D to contain 1. The same radius works for P_V. If
P_V(x),P_V(y) agree on gD and g is outside V, they already recover
x(g)=y(g). If g is in V, their zero-filled F-images agree on gD:
on V by assumption and off V because guard preservation makes both
zero. The inverse radius of F recovers x(g)=y(g).

The finite-mask theorem now makes P_V bijective. It preserves its
exterior coordinates, so its zero-exterior fiber is bijective too.
Every finitely supported target lies in a finite union V of H-cosets
and is therefore in the image of F. That image is compact and hence
closed, so F is onto.

For the precise finite-memory hypothesis, one can replace H by
H_0=<S intersect H>. If x vanishes on gH_0, choose z agreeing with
x on gS and vanishing on gH. The requirements agree on their overlap
g(S intersect H). Locality gives F(x)(g)=F(z)(g)=0. Thus H_0 is
also a guard; it is enough that H_0 be surjunctive.

This subsumes the preceding virtually abelian and polycyclic guard
proofs. In particular a construction with a free or other known
surjunctive guard cannot be a strict embedding merely because the
guard is nonamenable. No surjunctivity assertion about the arbitrary
ambient group G is made.
