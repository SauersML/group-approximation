# Virtually abelian guard subgroups: finite coset stratification

Date: 2026-09-08. This extends the positive guard theorem to all locally
virtually abelian subgroups, without commensuration in the ambient
group. The finite coset stratification proof first treats subgroups
virtually isomorphic to Z^r, for every finite r, including rank two.
A finite-memory reduction then gives the broader guard statement. It
does not settle Gottschalk surjunctivity for arbitrary cellular
automata. The proof below is mathematical; no computation was run.

Here “virtually Z^r” means that a subgroup isomorphic to Z^r has finite
index. The mask-stratification theorem requires this finite-generation
condition. The final CA guard corollary also covers infinitely generated
abelian groups such as Q^r, because only finitely many guard addresses
occur in the memory.

## The guard theorem

Let A be a finite alphabet with distinguished symbol 0, let G be any
group, and let H<=G be virtually Z^r with r finite. Suppose a cellular
automaton F:A^G -> A^G preserves configurations supported in every
union of cosets gH. If F is injective, then F is surjective.

Equivalently, the support assumption is that F(x)(g)=0 whenever x
vanishes on gH. As in the cyclic result, a polynomial rule with no
constant term satisfies this hypothesis if every monomial contains
an operand whose address belongs to H.

The proof uses a stronger intermediate statement about nonuniform
local maps. Its uniform injectivity hypothesis is essential to the
argument and is verified explicitly for the maps arising from F.
No assertion about arbitrary injective nonuniform cellular automata
on amenable coordinate sets is used.

## Local maps with finitely many coset masks

Write cosets in the form C_i=K_i a_i, so K_i is their left stabilizer.
Assume every K_i is virtually Z^(r_i), where r_i is finite. A map
P:A^G -> A^G has finite coset masks if there are finitely many C_i,
a finite memory set M containing 1, and finite local rules f_eta such
that

    P(x)(g)=f_(eta(g))((x(gs))_(s in M)),
    eta_i(g)=1_(C_i)(g),
    f_0((z_s))=z_1.                                  (1)

Thus P is the identity outside the finite union of its masks. The
local rules can depend arbitrarily on the mask bit pattern.

Call P uniformly injective if some finite D, containing 1, satisfies

    P(x)|_(gD)=P(y)|_(gD)  implies  x(g)=y(g)          (2)

for every g,x,y. This says that the inverse on the image has one
finite spatial radius valid at every coordinate. Uniform injectivity
implies ordinary injectivity.

**Stratification statement.** Every uniformly injective map of form
(1) is bijective.

Several closure facts will be used with their actual spatial scope:

* Right-translating a mask K_i a_i by s^-1 gives K_i a_i s^-1, with
  exactly the same left stabilizer.
* If two masks K_i a_i and K_j a_j meet at w, their intersection is
  (K_i intersect K_j)w. This is a single coset, not an arbitrary subset.
* A subgroup of a group virtually Z^r is virtually Z^d for d<=r.
  It has rank r exactly when it has finite index. Thus two rank-r
  stabilizers with a rank-r intersection are commensurate.

These elementary facts ensure that the finite intersections used
below stay in the stated class and strictly lower rank when required.

## Isolating one maximal-rank class

Let r be the largest rank of a mask stabilizer, and partition the
rank-r stabilizers into commensurability classes. Fix one class j,
and let

    L=intersection_(i in class j) K_i,
    U=union_(i in class j) C_i.

Then L is virtually Z^r and has finite index in each K_i in that
class. Consequently U is a finite disjoint union of free left
L-orbits. Every class-j mask is invariant under left translation by L.

Define P_j by setting all non-j mask bits to zero in (1), while
retaining the actual class-j bits. This is an L-equivariant local
map, and it fixes every coordinate outside U.

The map P_j inherits the same uniform injectivity radius D as P.
Here is the limit argument, including the needed avoidance statement.
For a finite window W and a non-j mask C_i, the condition

    h w in C_i,     h in L,     w in W

puts h in a coset of L intersect K_i, when that set is nonempty.
This intersection has rank less than r: either K_i already has lower
rank, or it belongs to a different maximal-rank class. Finitely many
such cosets cannot cover L. To verify this without a density claim,
pass to a finite-index lattice Z^r in L. Its intersection with each
forbidden coset is empty or an affine coset of a lower-rank subgroup.
Choose an integer direction outside the finitely many associated
proper rational subspaces. The integer line in that direction meets
each forbidden affine coset at most once, so some point avoids all.

Thus a left translation by a suitable h in L preserves every class-j
mask and makes all other mask bits zero throughout W. Conjugating P
by that translation gives exactly the output rules of P_j on W.
Such conjugates obey (2) with the same D. Applying this observation
to W=gD shows that agreement of P_j(x),P_j(y) on gD implies x(g)=y(g).
This establishes uniform injectivity of P_j. It uses a fixed local
inverse radius, not the generally false claim that ordinary
injectivity is closed under coefficient limits.

## The isolated periodic map is bijective

First set all coordinates outside U to zero. Since P_j fixes those
coordinates, this is an invariant fiber. On U it is a cellular
automaton over L with finitely many tracks: write

    U=disjoint union_(q=1)^m L r_q.

At an output h r_q, a memory address h r_q s either lies outside U,
where the input is zero, or has the form h l r_p for a fixed l in L.
There are finitely many q,s. Hence this is a genuine finite-alphabet
CA over L with finite memory, not a rule with infinitely many tracks.
It is injective by (2), and L is amenable, so it is surjective.

The standard input here is the Myhill theorem for amenable groups:
an injective finite-alphabet CA is surjective. A stronger semigroup
version is proved by Ceccherini-Silberstein and Coornaert in
[The Myhill property for cellular automata on amenable semigroups](https://arxiv.org/abs/1302.5965).

Now fix any finitely supported exterior configuration c on G minus U.
The corresponding fiber map on U differs from the zero-exterior map
at only finitely many output coordinates: a difference requires a
memory address to meet supp(c). It remains injective. Composing it
with the inverse zero-exterior map gives an injective map fixing the
complement of a finite set E. On each fixed exterior-of-E fiber, this
is an injective self-map of the finite set A^E and is therefore
bijective. Thus every finitely supported exterior fiber is bijective.

The image of P_j consequently contains every configuration whose
restriction to G minus U has finite support. These configurations
are dense in A^G. Continuity and compactness make the image closed,
so P_j is surjective on the full space, and hence bijective.

Its inverse has finite memory by (2). It is L-equivariant because
P_j is, and it fixes the complement of U. Therefore its output rule
has only finitely many possibilities: one for each orbit L r_q in U,
and the identity rule outside U. In particular P_j^-1 itself has
finite coset masks, all with stabilizer L and hence all in class j.
This verifies the inverse closure required by the next step.

## Cancellation removes one maximal-rank class

Set

    R=P composed with P_j^-1,
    W=union_(i not in class j) C_i.

The composition has finite memory and finitely many coset masks.
Besides the original masks of P, the inverse contributes right
translates of masks L r_q, so their stabilizers are still in class j.

Crucially, R fixes every coordinate outside W. Indeed, at g outside W
all original non-j bits vanish. The output rules of P and P_j at g
are then identical for every input. Therefore

    R(x)(g)=P_j(P_j^-1(x))(g)=x(g).

For the coefficient description of R, replace every class-j mask C
by C intersect W. On W this does not change the mask bits, and off W
the output is already the identity. Each replacement is a finite
union of cosets C intersect C_i with i not in class j. Every such
intersection has rank less than r, by the closure facts above.
Thus R admits a description of form (1) with one fewer rank-r
commensurability class. All new masks have strictly smaller rank.

The map R is uniformly injective. Its inverse on its image is the
composition of the local inverse of P on its image with the local
map P_j; both have finite spatial radius. Equivalently, one can
apply (2) for P at the finitely many input sites required to evaluate
P_j. No inverse with uncontrolled radius is introduced.

Induct lexicographically on the largest rank and the number of
classes of that rank. When rank is zero, every mask is finite, so P
fixes the complement of a finite set and ordinary injectivity already
implies bijectivity by the finite-fiber argument. In the inductive
step, R is bijective by the preceding reduction, and

    P=R composed with P_j

is bijective. This proves the stratification statement for every
finite maximal rank, in particular ranks one and two.

## Applying the statement to a guard subgroup

Return to the injective CA F and let V be a finite union of H-cosets.
Define a map P_V on all configurations by zero filling the input
outside V, applying F on V, and preserving the original exterior:

    z(g)=x(g) if g in V, and z(g)=0 otherwise;
    P_V(x)(g)=F(z)(g) if g in V, and P_V(x)(g)=x(g) otherwise.

This map has finite coset masks. If S is the memory of F and
V is the union of cosets g_i H, it is enough to use masks g_i H
and g_i H s^-1 for s in S. Their left stabilizers are the conjugates
g_i H g_i^-1, all virtually Z^r. If all masks vanish at g, then g
is outside V and the output is x(g), as required by (1).

It remains to check the stronger hypothesis (2). Global injectivity
of a CA on the compact full shift gives a finite inverse radius D
on its image: otherwise pairs disagreeing at 1 with images agreeing
on arbitrarily large finite sets would have a compactness limit
contradicting injectivity. Equivariance makes the same D work at
every g; enlarge it to contain 1.

Suppose P_V(x),P_V(y) agree on gD. If g is outside V, then x(g)=y(g)
because that coordinate is preserved. If g belongs to V, form the
two zero-filled inputs z,z'. Their F-images agree on gD: on V this
is the given agreement, and outside V both images are zero by guard
support preservation. The inverse radius for F then gives
z(g)=z'(g), hence x(g)=y(g). This proves uniform injectivity of P_V.

The stratification statement makes P_V bijective. Since it preserves
its exterior coordinates, its zero-exterior fiber is bijective as
well. Thus the restriction of F to configurations supported in V is
surjective onto those configurations. Every finitely supported target
lies in some finite union V of H-cosets, so all such targets are in
the image of F. Compactness of that image proves surjectivity on A^G.

The lower-rank intersections may be infinite, including entire
infinite cyclic cosets in the rank-two case. They are handled by the
finite rank/class induction, not by treating them as finite output
perturbations or assuming equivariance under a trivial intersection.

The preceding cyclic and commensurated guard results are recorded in
`research/artifacts/gottschalk-quadratic-block-elimination-2026-09-08.md`.

## Finite-memory reduction and locally virtually abelian guards

For the guard hypothesis itself, the whole subgroup H is unnecessary.
Let S be a finite memory set for F and define

    H_0=<S intersect H>.

Then support preservation on unions of H-cosets implies support
preservation on unions of H_0-cosets. Indeed, suppose x vanishes on
gH_0. Choose a configuration z that agrees with x on gS and vanishes
on gH. These requirements are consistent: their overlap is g(S
intersect H), which lies in gH_0 and therefore already has value zero
in x. Locality and the original guard condition give

    F(x)(g)=F(z)(g)=0.

This proves the guard condition for H_0 at every g. No inverse rule,
finite-index assumption, or commensuration is needed in this reduction.

Consequently the guard theorem holds whenever every finitely generated
subgroup of H is virtually abelian: H_0 is finitely generated and
virtually abelian, hence virtually Z^r for some finite r, so the theorem
already proved applies. In particular it holds for every abelian H,
whether or not H is finitely generated or has finite rank.

More precisely, it is enough that the single subgroup <S intersect H>
is virtually abelian. No claim about the structure of the rest of H
is then required.

## The coset-mask hypothesis cannot be replaced by amenability

There is an exact control showing why uniform local recoverability
alone does not make nonuniform local maps on amenable sets surjective.
Take a finite alphabet A with at least two symbols and distinguished
zero, and define P:A^Z -> A^Z by

    P(x)(n)=x(n)       for n<=0,
    P(x)(1)=0,
    P(x)(n)=x(n-1)     for n>=2.

This has finite spatial memory {0,-1}. The local map

    J(y)(n)=y(n)       for n<=0,
    J(y)(n)=y(n+1)     for n>=1

satisfies J composed with P=Id and has finite memory {0,1}.
Thus P is uniformly injective in precisely the sense used above.
Nevertheless every output has value zero at coordinate 1, so P
is not surjective.

The obstruction to applying the stratification theorem is exact:
P's half-line coefficient pattern is not determined by finitely many
cosets of subgroups of Z. Every such coset is either a singleton or
a two-sided arithmetic progression. A Boolean combination of finitely
many of them is periodic outside a finite set, with the same residue
pattern on both tails. The identity rule on the negative tail and
the shift rule on the positive tail cannot have this form. These
rules differ as functions on the full local input alphabet because
A has at least two symbols.

This control preserves both amenability of the coordinate group and
a uniform local decoder. It rejects dropping the finite-coset-mask
condition from the nonuniform statement.

## Uniform recoverability alone does not imply surjectivity

The finite-coset coefficient hypothesis is substantive. On a finite
alphabet with at least two symbols, define a nonuniform local map on Z by

    P(x)(n)=x(n)      for n<=0,
    P(x)(1)=0,
    P(x)(n)=x(n-1)    for n>=2.

It has the uniformly local left inverse

    J(y)(n)=y(n)      for n<=0,
    J(y)(n)=y(n+1)    for n>=1.

Thus JP=id, but P is not surjective because its coordinate at 1 is
always zero. Even uniform recoverability over an amenable ambient group
does not replace the finite-coset-mask assumption.

This coefficient pattern uses a half-line. A Boolean combination of
finitely many subgroup cosets in Z is periodic outside a finite set:
the infinite cosets have a common period, and the remaining masks are
singletons. It cannot give the identity rule on one infinite tail and
the shift rule on the other. The example therefore lies outside the
coefficient class proved surjunctive above.
