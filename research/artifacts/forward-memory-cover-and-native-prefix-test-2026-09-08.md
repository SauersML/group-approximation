# One composition rectangle suffices for a surjunctive-cover obstruction

Date: 2026-09-08. Exact handwritten proof and a bounded construction
interface. No code, search, build, or new experiment was run for this
artifact. The proposed feedback rule in Section 6 is not asserted to
be injective. Only the implications in Sections 1-5 are proved.

## 1. The forward-table theorem

Use the convention that a CA with memory M computes at g from the
input on gM. Let tau,sigma:A^G->A^G have finite memories M,S, both
containing 1, and local functions f:A^M->A and d:A^S->A. Assume

    sigma tau=id.                                    (1)

Let H=<M union S>. The same rules define tau_H,sigma_H on A^H.
Over G the rules act independently on each left H-coset gH, so
their composition identities hold over G exactly when they hold
over H. This also transfers a strict reverse defect between them.

Suppose pi:P->H is an epimorphism, P is surjunctive, and each memory
element a has a chosen lift a~ with 1~=1. Assume

    pi is injective on S~ M~.                         (2)

Use the same f,d to define tau_P,sigma_P over P. At the identity,
their composition reads the positions s~m~. The map pi sends this
finite set bijectively to SM: it is onto by the lift choices and
injective by (2). Hence an arbitrary pattern on S~M~ determines a
pattern on SM with exactly the same coincidences. Extend that target
pattern arbitrarily to A^H and apply (1). It follows that

    sigma_P tau_P=id.                                (3)

The recovered identity coordinate is preserved since both memories
contain their marked identity. Translation gives (3) at every site.
Thus tau_P is injective. Surjunctivity of P makes it bijective, and
(3) then implies

    tau_P sigma_P=id.                                (4)

Pullback pi^*:A^H->A^P is defined by (pi^*x)(p)=x(pi(p)). It is
injective since pi is onto, and direct substitution in the local
rules gives

    tau_P pi^*=pi^* tau_H,
    sigma_P pi^*=pi^* sigma_H.

Consequently (4) implies pi^* tau_H sigma_H=pi^*. Injectivity of
pi^* proves tau_H sigma_H=id, and coset localization proves the same
over G. This proves the claim.

Nothing here assumes pi injective on M~S~. Equalities of functions
on the more independent source variables remain true when target
variables are identified. This is exactly why the reverse rectangle
requires no separate comparison when there is a genuine group map.
For two arbitrarily marked finite tables with no compatible group
map, that argument is not available.

## 2. A finite presentation built only from forward equalities

Let V=(M union S) minus {1}. Form the group

    U_SM=<x_a (a in V) |
       x_s x_m=x_s' x_m' whenever sm=s'm' in G>,       (5)

where x_1 means the empty word. The assignment x_a->a gives an
epimorphism U_SM->H. In particular distinct elements of V cannot
collapse together in U_SM. Products x_s x_m are equal exactly when
the corresponding products sm are equal in H: one implication is
imposed in (5), and the other follows by applying the epimorphism.
Thus the forward table in U_SM is exactly the one needed for (3).

The identical f,d therefore give sigma_U tau_U=id. If the original
tau sigma differs from id, then tau_U sigma_U also differs from id,
because an identity upstairs would descend by pullback as above.
So any supplied strict pair produces a nonsurjunctive U_SM with the
same finite alphabet and memory cardinalities. No preservation of
all other target inequalities or reverse product classes is claimed
or needed; target inequalities automatically persist upstairs.

For each equivalence class of S x M under (s,m)~(s',m') iff
sm=s'm', choose one anchor and equate every other pair to it.
This gives |S||M|-|SM| relations. Each is a word of length at most
four in the memory generators, sometimes shorter because x_1=1.
The presentation has |M union S|-1 generators. It is explicit once
the finite product table is supplied; no decision procedure for
arbitrary group equality is asserted.

This is a necessary finite presentation for a successful pair,
not a proof that all presentations of this form are surjunctive.

## 3. The two already-excluded atlas seeds need only forward checks

For the first seed, the canonical two-chart map

    A8*A8 -> Q=L_(F_2)(1,2)^x

is onto. The four marked atlas generators generate Q. Their encoder
memory together with identity, and its inverse decoder memory, have
an exact forward product table in this cover. Since a free product
of finite groups is virtually free and surjunctive, Section 1 already
excludes a strict pair. Its reverse-table check is a useful consistency
check but not a hypothesis needed by this proof.

For the fresh-V4 seed put

    A0=[q13(e),q32(e*)],
    B0=[q13(f),q32(f*)],
    C0=[q13(1),q32(1)].

The actual root identities give A0=x12(ee*), B0=x12(ff*), and
C0=x12(1), where ee*+ff*=1. The elements A0 and B0 are commuting
involutions and A0 B0=C0, so the marked map from a fresh V4 factor
to Q is a homomorphism. Together with the atlas map this gives the
genuine epimorphism

    (A8*A8)*V4 -> Q.

The saved forward partition has no additional target identifications.
Section 1 again suffices. It is not enough for a future seed to
introduce new collisions only into MS while retaining such a lift
on SM.

The relevant exact saved tables are
`experiments/gottschalk-atlas-first-seed-2026-09-08.json` and
`experiments/gottschalk-atlas-fresh-v4-seed-2026-09-08.json`.
This proof imports no new numerical conclusion from them.

## 4. How a prefix chain forces an internal word relation

Let M contain 1 and each letter t_i in an actual relation

    R=t_1 ... t_l=1 in G.

Put p_0=1 and p_j=t_1...t_j, and include all p_0,...,p_(l-1) in S.
Repeated prefixes are simply one address. The forward table contains
the consecutive equalities

    p_(j-1) t_j = p_j 1,             1<=j<=l,         (6)

where p_l=p_0. In U_SM, equations (6) imply inductively
x_(p_j)=x_(t_1)...x_(t_j), and the final equation forces
x_(t_1)...x_(t_l)=1. Thus the table authenticates the internal word
R rather than merely giving its value a fresh name. Other forward
coincidences may impose additional relations.

Here is a concrete twelve-step Leavitt word. Set

    x=q13(e),     y=q32(e*),
    z=q13(f),     w=q32(f*),
    v=q13(1),     u=q32(1).

Each is an involution. The relation A0 B0=C0 becomes

    R=x y x y z w z w u v u v=1.                     (7)

In the standard two-chart dictionary x,z,u belong to chart 1 and
y,w,v belong to chart 2. All twelve factors are nonidentity and
alternate charts, so (7) is a nontrivial reduced word in A8*A8.
The prefix construction therefore makes it impossible to lift the
whole forward table to that source with these primitive letters in
their native charts. The same is true of those native lifts in
(A8*A8)*V4, since its A8*A8 free factor embeds.

This excludes those particular marked lifts, not every possible
surjunctive cover or every alternate choice of lifts. Failing one
cover test is necessary progress toward a candidate, not a proof of
injectivity or strictness.

## 5. A positive-root-only version is still impossible

The six letters in (7) alone cannot support a strict encoder. They
lie in one finite subgroup, despite the authentic Leavitt relation.
In the coordinate order (1,3,2), they generate an upper unitriangular
three-by-three group over the characteristic-two Leavitt ring.

Indeed let A0 be the F_2-span of {e,f,1}, B0 the span of {e*,f*,1},
and C0 the span of their nine pairwise products. Every word in the
six generators has a unique matrix shape

    [[1,a,c],[0,1,b],[0,0,1]],
           a in A0, b in B0, c in C0.                (8)

Multiplication changes the third coordinate by c+c'+ab'; this stays
in C0. Inversion has the same form. These three spaces have
dimensions at most 3,3,9, so there are at most 2^15 matrices in (8).
Their image in the Leavitt unit group is finite as well.

An encoder whose effective memory lies in this subgroup acts
independently on its finite cosets. If globally injective, each
finite-alphabet map on one coset is injective and hence surjective.
Thus even a fully authenticated positive-root cell does not by
itself provide an eligible encoder actor. Extra addresses that the
local rule never reads do not fix this defect: the effective memory
is the one relevant to the localization argument.

## 6. The bounded feedback candidate has an explicit collision

The following rejected candidate keeps the original four full-actor
generators a1,b1,a2,b2, includes all six primitive letters of (7) in
the effective nonlinear memory, and exposes (7) in the decoder table.

For binary tracks define

    J(U,V)(g)=U(ga1)V(gb1)+U(ga2)V(gb2)
             +U(gx)V(gy)+U(gz)V(gw)
             +U(gv)V(gu)+U(g)V(g).

On four tracks, the candidate rule is

    F_i=X_i+J(X_(i+1),X_(i+2)),       i modulo four.   (9)

Its encoder memory lies in the eleven-element list

    M={1,a1,b1,a2,b2,x,y,z,w,u,v}.

The six displayed address pairs are distinct: the primitive roots
are distinct involutions, while the four established chart words
have order three. Thus the native primitive inputs and the full-
actor inputs actually occur in the Boolean local function. Constants
are fixed because the six quadratic contributions cancel there;
every coordinate axis is fixed because every nonlinear term reads
two different tracks. These checks do not establish injectivity.

Take decoder memory S=M union {p_0,...,p_11}, for the prefixes of
(7). It has at most 21 elements, since both 1 and p_1=x already
lie in M. The native-chart forward lift is excluded by Section 4,
and the finite-subgroup encoder obstruction of Section 5 is avoided
because the effective encoder memory retains all four generators of
Q. Other surjunctive-cover obstructions have not been excluded.

The exact boundary calculation in
[the native second-marginal collision proof](gottschalk-native-second-marginal-collision-2026-09-08.md)
now supplies a binary configuration U with

    U(1)=1,       J(1,U)=U.

Set V=1+J(U,1). Bilinearity gives the full collision

    F(U,1,U,1)=(0,V,0,V)=F(0,V,0,V).                 (10)

The inputs differ because U(1)=1. Thus no left inverse exists, of any
degree or memory. The candidate no longer has an unresolved decoder
search obligation. The proof gives all five prefix identities defining
the boundary mask, and applies to every even feedback cycle with this
second-argument marginal on the odd outputs, even if first-argument
addresses and even-output operations change. A new candidate must escape
that shared marginal obstruction, as well as the cover tests above.

## 7. Prior-work and endpoint boundary

Repository search located the two-rectangle formulation in
`gottschalk-nonlinear-ca-search-2026-08-24.md` and the marked-limit
proof in `gottschalk-surjunctivity-fixed-tester-proof`. The former
uses both product partitions for a general finite rule search; the
latter transports finite witnesses through marked limits. Section 1
isolates the stronger one-rectangle condition available when a
genuine surjunctive cover and specified local decoder are supplied.

The general local-approximation principle is classical. Glebsky and
Gordon, [On surjunctivity of the transition functions of cellular automata on groups](https://doi.org/10.11650/twjm/1500407858),
prove surjunctivity for groups approximable by amenable groups. Their
2005 paper was checked as primary-source context on 2026-09-08.
No novelty claim for group-quotient functoriality or the general
finite-witness method is made here.

The present proof gives a sharper rejection condition and an exact
necessary finite presentation for a strict pair. Its prefix-chain
application identifies a concrete mixed relation that a new memory
window can force. The specific rule (9) is now noninjective. A new
eligible encoder and its local inverse and reverse-defect witnesses
remain to be constructed; the unrestricted Gottschalk and Leavitt
nonsurjunctivity roots remain open.
