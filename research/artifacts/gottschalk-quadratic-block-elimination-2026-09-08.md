# Quadratic feedback: positive block elimination and its precise limits

Date: 2026-09-08. Consolidated independent proof audit and attack artifact.
No computation is used. This does not settle Gottschalk's conjecture or
construct a nonsurjunctive cellular automaton.

Throughout, G is any group and k is a finite field. Tracks are elements
of k^G. A bilinear operation means a G-equivariant finite-memory map
bilinear over k in its two track arguments. Different terms may use
different operations and spatial memories.

The only prior structural input is
[nonlinear-certificate-fibers-are-all-surjective-or-all-strict](../nonlinear-certificate-fibers-are-all-surjective-or-all-strict.md):
an injective full-shift CA preserving a certificate track is surjective
if one certificate fiber is bijective. A bijective CA has a local inverse.

## Generalized two-block lemma

Suppose

    F(X,Y)=(L_Y X,V(X,Y))

is a CA, where L_Y is homogeneous linear in the entire X block for each
fixed Y. Assume:

1. The zero-X restriction v_0:Y -> V(0,Y) is bijective.
2. For one certificate configuration Y_0, L_(Y_0) is bijective.

Then injectivity of F forces surjectivity.

Indeed, if L_Y X=0, surjectivity of v_0 supplies Y' with
v_0(Y')=V(X,Y). Thus F(X,Y)=F(0,Y'). Injectivity gives X=0. Since L_Y
is linear, it is injective for every Y. Consequently

    E(X,Y)=(L_Y X,Y)

is an injective certificate-preserving CA. Its Y_0 fiber is bijective,
so the certificate-fiber theorem makes E bijective with a local inverse.
Now F E^-1 preserves its first block. Its first-block-zero fiber is
v_0, since L_Y^-1(0)=0. A second application of that theorem makes
F E^-1, and hence F, surjective.

In particular, both axes need not be fixed pointwise. A bijective
zero-X restriction suffices, provided the one known coefficient fiber
has also been authenticated.

## Bipartite operand graphs

Consider a quadratic rule

    F_i(x)=x_i+sum_(j,k) B_(i;j,k)(x_j,x_k),

with j distinct from k in every summand. Form the operand graph on track
indices: an edge joins j to k whenever they occur together in any
quadratic term, regardless of the receiving output i.

If this graph is bipartite, every injective such F is surjective.
Group its two color classes into X and Y. Every quadratic term contains
exactly one track from each class. Therefore the X output is homogeneous
linear in X for fixed Y, F fixes both coordinate axes, and L_0=id. The
two-block lemma applies. Isolated tracks may be assigned either color;
if there are no edges the map is the identity.

This covers arbitrary bipartite operand graphs and arbitrary recipients,
not just a nearest-neighbor cycle of track labels.

## Target-multiplicative systems

Every injective CA of the form

    F_i(x)=x_i+sum_(j distinct from i) B_(i,j)(x_i,x_j)       (1)

is surjective, with no restriction on the directed control graph.

Prove this by induction on the number of tracks. For one track the map
is the identity. For more tracks take X=x_1 and let Y be all others.
The first output is homogeneous linear in X and L_0=id. Setting X=0
makes the first output zero and leaves on Y another system of form (1).
Its injectivity follows from injectivity of F; induction makes it
bijective. The generalized two-block lemma now finishes the proof.

The condition j distinct from i is essential. Bilinear dependence on two
shifted copies of the target itself is not homogeneous linear in that
track. The reversible example below shows this is a substantive issue.

## Arbitrary-length cyclic nearest-two feedback

Let m>=3, with indices modulo m, and consider

    F_i(x)=x_i+B_i(x_(i+1),x_(i+2)).                         (2)

For arbitrary bilinear B_i, injectivity of (2) forces surjectivity over
every group.

For even m, the odd and even track classes make the operand graph
bipartite, so the preceding result applies.

For odd m make the reversible input shear

    x_1_old=z_1-B_1(x_2,x_3),

leaving the other tracks unchanged. The first output becomes z_1. On
its zero fiber put

    X=(x_2,x_4,...,x_(m-1)),
    Y=(x_3,x_5,...,x_m).

Every ordinary X output has one X and one Y operand. The final X output
has the additional nested term

    -B_(m-1)(x_m,B_1(x_2,x_3)),

which is still homogeneous linear in X for fixed Y. The final Y output
may contain

    -B_m(B_1(x_2,x_3),x_2),

which can be quadratic in X; this is allowed by the lemma. Every nonlinear
term vanishes on both coordinate axes, and the X coefficient at Y=0 is
the identity. Thus the zero-z_1 fiber is bijective under injectivity.
The preserved-z_1 certificate-fiber theorem makes the whole transformed
map bijective. Undoing the shear proves the assertion.

This argument includes m=3 and does not require the B_i to agree or to
be alternating.

## A genuine same-track quadratic reversible control

Over k=F_2, suppose t in G has order three. The scalar rule

    Phi_t(x)(g)=x(g)+x(g)x(gt)+x(gt)x(gt^2)                   (3)

is nonlinear and reversible. It acts independently on each coset g<t>.
On its three bits it fixes 000, 111, and all weight-one
patterns, while cyclically permuting the three weight-two patterns.
Hence Phi_t^3=id. Its local inverse is

    Phi_t^-1(x)(g)=x(g)+x(g)x(gt^2)+x(gt)x(gt^2).

Thus an assertion that an injective binary quadratic rule must be affine
is false. Same-track terms are already a one-track escape from the
bipartite grouping and target-multiplicative criteria.

## A minimal loop-free mixed triangle

If same-track quadratic terms are excluded, at most two tracks always
give a bipartite operand graph. A first three-track pattern outside the
initial grouping and target-isolation moves is

    F_1=x_1+A_12(x_1,x_2)+A_23(x_2,x_3),
    F_2=x_2+B_23(x_2,x_3)+B_31(x_3,x_1),
    F_3=x_3+C_31(x_3,x_1)+C_12(x_1,x_2).                    (4)

Each row contains both a target-dependent term and a target-free term.
No row is isolated by the elementary input shear used for (2), and no
proper block of the displayed tracks has homogeneous-linear outputs.
This statement only concerns the specified initial moves.

There is a rigorous version allowing every constant linear track change
before that first move. Take each of the six operations in (4) to be one
product x_j(gs)x_k(gt), with s distinct from t, and give the six terms
pairwise distinct unordered spatial address pairs {s,t}, as actual
elements of G. Then their coefficient tensors remain separated under
constant linear changes of track coordinates.

No target-free coordinate can then be isolated in any constant linear
basis. If a nonzero output linear combination were independent of an
input direction v, choose one row participating in that combination.
Its two terms involve all three operand coordinates. Independence of
each separated tensor from v forces each of those three coordinate
functionals to vanish on v, hence v=0, a contradiction.

Nor is there a homogeneous-linear proper block after a constant linear
conjugacy. Write the proposed decomposition as k^3=X direct-sum Y.
For each term whose target vector has nonzero projection onto X, absence
of pure-X and pure-Y quadratic terms forces its two operand coordinate
functionals to lie in opposite summands of the dual decomposition. Any
active row uses all three coordinate functionals, so the decomposition
must be a coordinate partition. If X is a singleton, its row's foreign
operand pair lies entirely in Y. If X has two coordinates, an edge within
X occurs in one of those two output rows. Both contradict the required
crossing condition.

These are obstructions to a constant linear track conjugacy followed by
one target-free isolation or homogeneous-block move. They do not exclude
arbitrary nonlinear reversible rewrites or track shifts, and they prove
neither injectivity nor strictness of an instantiated rule.

## Reversible controls for the mixed triangle and distinct-pair condition

Taking all six operations in (4) to be pointwise multiplication gives
exactly the three-bit permutation from (3). It is reversible. Moreover,
at x_2=1 the coefficient of x_1 in its first output is zero. Thus global
injectivity does not imply injectivity of every affine target slice:
other outputs can recover the apparently lost bit. The zero-axis image
condition in the two-block lemma cannot simply be omitted.

The distinct-pair condition can also hold in a reversible example. Start
with that pointwise order-three permutation Phi, and conjugate by
independent track shifts S(x)_i(g)=x_i(gs_i). Then S^-1 Phi S has, for a
term with target i and operands j,k, address gains

    (s_i^-1 s_j, s_i^-1 s_k).

For s_1=1,s_2=a,s_3=b in the free group on a,b, its six unordered pairs are

    {1,a}, {a,b},
    {1,a^-1 b}, {a^-1 b,a^-1},
    {1,b^-1}, {b^-1,b^-1 a}.

They are pairwise distinct, with distinct addresses inside each pair.
The resulting CA remains order three, despite resisting the constant
linear initial moves proved unavailable above. Its gains satisfy
g_ij g_jk=g_ik and g_ii=1. A proposed new instantiation should at least
test this simple track-shift conjugacy, and should then prove its actual
decoder or exhibit a collision. An escape from one elimination scheme
does not supply either result.

## All scalar two-term selectors are surjunctive

A different argument gives a complete positive exclusion beyond the
track-grouping criterion. For arbitrary t,u in G, let

    T_(t,u)(x)(g)=x(g)+x(g)x(gt)+x(gt)x(gu),                 (5)

over F_2. This is the selector which reads x(g) when x(gt)=0 and x(gu)
when x(gt)=1. If (5) is injective, it is surjective.

First dispose of coincident addresses:

* If u=1, the two quadratic terms cancel and T is the identity.
* If t=1 and u differs from 1, T(x)=x R_u x. Both zero and the
  single-particle configuration delta_1 map to zero.
* If t=u differs from 1, T is Boolean OR of x and R_t x. The all-one
  configuration and the configuration with just one zero have the same
  all-one output.

Now assume 1,t,u are pairwise distinct. Compare x and x+delta_1.
Their outputs can differ only at 1,t^-1,u^-1, and the three differences
at those sites are respectively

    1+x(t),
    x(t^-1)+x(t^-1 u),
    x(u^-1 t).                                           (6)

None of the variables displayed in (6) is x(1), by distinctness. Thus a
single-bit collision exists whenever one can consistently impose

    x(t)=1,   x(u^-1 t)=0,   x(t^-1)=x(t^-1 u).            (7)

The two pinned sites are distinct, and so are the two sites required
equal. The only inconsistency is therefore

    {t^-1,t^-1 u}={t,u^-1 t}.                             (8)

If (8) fails, assign the finitely many bits in (7), set the rest to zero,
and obtain an explicit finite-support collision with its flip at 1.
The two possible matchings in (8) give exactly

    u=t^2,

or

    t^2=1 and t u t=u^-1.                                (9)

There is a separate obstruction to infinite or even order of u. Direct
Boolean expansion gives

    T(x)+T(1+x)=1+x+R_u x.                               (10)

If u has infinite or even order, choose x alternately along every coset
g<u>, so R_u x=1+x. Equation (10) then gives a collision between x and
its complement. Consequently injectivity forces u to have finite odd
order n.

Combine this with (9). If u=t^2, then t^(2n)=1, so <t,u> is finite
cyclic. In the other case <t,u> is a quotient of the finite dihedral
group of order 2n. Thus, apart from the identity case u=1, every injective
selector (5) has its memory contained in a finite subgroup H=<t,u>.
The rule acts independently and identically on each finite coset gH.
Global injectivity forces the finite map F_2^H -> F_2^H to be injective,
hence bijective. Its cosetwise inverse proves surjectivity of (5).

This does not classify which of the remaining finite cyclic or dihedral
cases are injective; that classification is unnecessary for the positive
statement. The order-three reversible control (3) is included by taking
u=t^2. The proof uses explicit collisions and finite coset dynamics,
rather than a claim that same-track quadratic dependence is linear.

## Finite guard subgroups

There is another direct positive criterion. Suppose a scalar polynomial
CA has linear term x(g), no constant term, and every nonlinear monomial
contains some operand x(gh) with h in one fixed finite subgroup H of G.
Then injectivity forces surjectivity.

Indeed, let V be any finite union of cosets gH. If an input vanishes
outside V, then at every g outside V the linear term vanishes and each
nonlinear monomial has a zero guard operand. Thus the finite configuration
space k^V, extended by zero outside V, is mapped into itself. Under
injectivity its restriction is a bijection of this finite set. Every
finitely supported target lies in one such V and is therefore attained.
The image of a CA is compact, so density of finite configurations gives
surjectivity on the whole full shift.

In particular, for arbitrary a,b,c,

    F(x)(g)=x(g)+x(gb)[x(ga)+x(gc)],

injectivity implies surjectivity whenever b has finite order. This covers
the seemingly more coupled choice u=a^-1 c of finite odd order together
with b=a u a^-1: its guard subgroup <b> is still finite. The argument does
not require the other two addresses to lie in that subgroup.

## Commensurated surjunctive guard subgroups

More generally, let the finite alphabet A have a distinguished symbol 0,
and suppose F preserves configurations supported in every union of
cosets gH. Equivalently, F(x)(g)=0 whenever x vanishes on gH. If H is
surjunctive and commensurated in a subgroup M containing H and the memory,
injectivity of
F forces surjectivity. The polynomial guard condition above implies
this support-preservation hypothesis, but polynomial form is unnecessary.
Here surjunctive means that every injective CA
on every finite-alphabet full shift over H is surjective; commensurated
means that H intersect gHg^-1 has finite index in both H and gHg^-1
for every g in M. Only the guard subgroup is assumed surjunctive.

First restrict to M, since the original rule acts independently on its
cosets. Let V be a finite union of distinct cosets g_i H in M, including
H itself. Configurations vanishing outside V again form an invariant
compact space A^V. Put

    H_0=intersection_i g_i H g_i^-1.

Commensuration makes H_0 finite index in every g_i H g_i^-1, and g_1=1
makes H_0 a subgroup of H. Surjunctivity passes to subgroups: extend a
CA on a subgroup independently to its cosets, apply surjunctivity of
the larger group, and restrict back. Thus H_0 is surjunctive.

The set V is a finite disjoint union of free left H_0-orbits. Identifying
these orbits with tracks turns the restriction to A^V into a CA on H_0
with a finite alphabet. Left H_0-equivariance is inherited from F, and
only finitely many orbit representatives and memory addresses occur;
addresses outside V are fixed at zero. Injectivity of F makes this
restricted CA injective, and surjunctivity of H_0 makes it surjective.
Every finitely supported target is contained in some V, so compactness
gives surjectivity on A^M and then on the original full shift.

In particular, amenable guard subgroups are surjunctive by the Myhill
theorem, a special case of [Ceccherini-Silberstein and Coornaert, The
Myhill property for cellular automata on amenable
semigroups](https://arxiv.org/abs/1302.5965). For the four-address scalar
rule this covers infinite-order b whenever <b> is commensurated in
<a,b,c>. Without commensuration, V can have infinitely many left
H_0-orbits, so this argument alone does not supply a finite-alphabet CA
over a known surjunctive group. The following finite-intersection
argument removes that restriction for cyclic guards.

## Finite intersections outside the commensurator

Keep the support-preservation hypothesis and suppose H is surjunctive.
Let C=Comm_M(H), the subgroup of elements commensurating H. Assume

    H intersect sHs^-1 is finite for every s in M outside C.          (11)

Then every injective F is surjective. This includes every virtually
cyclic H: an infinite subgroup of an infinite virtually cyclic group
has finite index, so an infinite intersection would put s in C. Such
H is amenable and therefore surjunctive. Finite H is already covered.

To prove the assertion, take any finite union V of H-cosets and partition
it into its intersections V_j with distinct C-cosets. On V_j define
B_j by applying F with all other coordinates fixed to zero. This is a
map into V_j by support preservation, and is injective by injectivity
of F. Translate one H-coset representative in V_j to 1. The resulting
finite union lies in C and contains H. Since H is commensurated in C,
the finite left-orbit argument of the preceding section proves that
this exact restriction B_j is bijective. This uses the restriction to
the finite union of H-cosets, not only surjectivity on the whole C-coset.
Consequently the product map B=product_j B_j is a bijection on A^V.

The actual restriction F_V differs from B at only finitely many output
coordinates. A difference can occur only at a site g in V_j for which
some memory address gs lies in a different V_k. Necessarily s lies
outside C. For two original H-cosets g_iH and g_lH, the sites at which
such a dependency occurs form the set

    {g in g_iH : gs in g_lH}.

If this set contains g_0, it is exactly

    g_0 (H intersect sHs^-1).

It is finite by (11). There are only finitely many pairs of H-cosets
and finitely many memory addresses, so the union E of all possible
cross-block output sites is finite.

The injective map F_V B^-1 fixes every coordinate outside E. For each
fixed configuration on V minus E, it therefore induces an injective
self-map of the finite set A^E, which is bijective. Thus F_V B^-1 and
F_V are surjective. This is the elementary finite-output perturbation
argument also used in
[finite-output-perturbation-proves-nonlinear-fiber-rigidity](../finite-output-perturbation-proves-nonlinear-fiber-rigidity.md).
Every finitely supported target belongs to some V. Compactness now
proves surjectivity of F on the entire full shift.

In particular, the scalar Boolean family

    F(x)(g)=x(g)+x(gb)[x(ga)+x(gc)]                         (12)

satisfies injectivity implies surjectivity for **every** group and
every choice of a,b,c, with no distinctness or order assumptions. Its
support is preserved on unions of cosets of the cyclic guard subgroup
<b>, and the theorem applies. More generally, over any finite field,
it applies to every scalar rule x(g)+x(gb)P(x), where P is any local
polynomial. This closes the entire single-cyclic-guard construction
family, including the infinite-b and noncommensurated cases; it does
not settle Gottschalk's conjecture for arbitrary cellular automata.

## Spatial bipartitions need not be periodic

There is a second whole-family positive theorem. Over a finite field k,
consider a scalar quadratic CA

    F(x)(g)=x(g)+sum_i lambda_i x(ga_i)x(gb_i),             (13)

where the nonzero coefficients and address pairs form a finite list.
Its spatial operand graph has vertex set G and an undirected edge
{ga_i,gb_i} for every g and i. If this graph is bipartite, injectivity
of F implies surjectivity. The coloring need not be periodic and need
not come from a finite-index subgroup of G.

Let C be the nonempty compact invariant subshift of all proper binary
colorings of this graph. Fix c in C and divide the input coordinates
into X, on color 0 sites, and Y, on color 1 sites. Every quadratic term
has one operand in each block. Hence F fixes both axes and has the form

    F_c(X,Y)=(L_(c,Y)X, V_c(X,Y)),

with L_(c,Y) homogeneous linear. If L_(c,Y)X=0, then

    F_c(X,Y)=(0,V_c(X,Y))=F_c(0,V_c(X,Y)).

Injectivity gives X=0, so every L_(c,Y) is injective. Thus the local
equivariant map E on C times k^G, defined by

    E(c,X,Y)=(c,L_(c,Y)X,Y),

is injective. For fixed c and finitely supported Y, the map L_(c,Y)
differs from the identity at only finitely many output sites. The finite
coordinate-fiber argument above makes it bijective. Finitely supported
Y are dense in the fixed-c Y space, so compactness makes L_(c,Y)
surjective for every Y. This proves E bijective on C times k^G.

Its inverse is uniformly local on this compact invariant subshift.
Indeed, its output coordinate at 1 is continuous into a finite set, so
compactness gives a finite determining set; equivariance translates
that same finite set to every other coordinate. Consequently changing
finitely many data coordinates while holding c fixed changes only
finitely many coordinates of E^-1.

Now D_c=F_c E_c^-1 preserves X and is the identity on the X=0 fiber.
For finitely supported X, its map on the Y fiber differs from the
identity at only finitely many output sites, by the locality just
proved. Injectivity and finite coordinate-fiber counting make that
fiber map bijective. Density of finitely supported X and compactness
then make every Y fiber surjective. Thus D_c, and hence F, is
surjective.

This proof never modifies the coloring certificate. All density and
finite-perturbation steps change only X or Y at a fixed proper coloring.
It therefore does not apply a full-shift certificate theorem to the
constrained coloring subshift without checking its hypotheses.

For the disjoint-pair Boolean family

    F(x)(g)=x(g)+x(ga)x(gb)+x(gc)x(gd),                    (14)

put u=a^-1 b, v=c^-1 d, and H=<u,v>. The operand graph has components
the cosets gH, with edges given by right multiplication by u and v.
It is bipartite exactly when there is a homomorphism

    chi:H -> F_2,   chi(u)=chi(v)=1.

One direction colors gH by chi after choosing a representative. For
the converse, bipartiteness says every relation in u,v and their
inverses has even length, so word length modulo two is well-defined
and supplies chi. This character need not extend to the full memory
subgroup <a,b,c,d>. This is a condition on the **operand graph**, not
on the directed graph from each output g to its input addresses.

## Complement collisions and finite 2-group quotients

For (14), Boolean expansion gives

    F(1+x)+F(x)=1+(R_a+R_b+R_c+R_d)x.                    (15)

Thus a solution of Lx=1, where L=R_a+R_b+R_c+R_d, gives an exact
collision between x and its complement. By compactness and finite
linear duality, failure of solvability is equivalent to a finite odd
set S of output sites satisfying

    Sa symmetric-difference Sb symmetric-difference Sc
       symmetric-difference Sd = empty.

Indeed, an inconsistent finite subsystem has a sum of rows with zero
left side and odd right side, and conversely any such row sum obstructs
a solution. Failure of this complement test does not prove injectivity.

In particular, let P be any finite 2-group quotient of the memory
subgroup. If alpha=a+b+c+d has nonzero image in F_2[P], then Lx=1
has a solution on P. Otherwise the preceding finite duality would give
f alpha=0 with augmentation(f)=1. Every augmentation-one element of
F_2[P] is a unit, contradicting alpha nonzero. To see this unit fact
directly, induct on |P|: choose a central element z of order two, pass
to F_2[P/<z>], and lift an inverse modulo the ideal (1+z). This ideal
has square zero, so an inverse modulo it corrects to an actual inverse.
The trivial-group base case is immediate.

Pulling the solution back from P gives a complement collision on the
original group. Therefore injectivity forces the four operand images
to occur with even multiplicity in every finite 2-group quotient.
If distinct elements of the memory subgroup can be separated by finite
2-group quotients and a,b,c,d are pairwise distinct, a finite product
of separating 2-group quotients
keeps them distinct. The resulting nonzero alpha forces noninjectivity.

## Acyclic output dependencies

There is also a direct sufficient condition for surjectivity of (14),
without any injectivity assumption: suppose no nonempty positive word
in a,b,c,d represents 1. The directed graph with edges g -> gs, for
s in {a,b,c,d}, is then acyclic. For any finite set of prescribed output
sites, fix all exterior input coordinates arbitrarily. The induced
finite dependency graph is acyclic, so solve its equations
x(g)=y(g)+x(ga)x(gb)+x(gc)x(gd) in reverse topological order. This
satisfies all prescribed output coordinates. Compactness supplies a
preimage of every full target.

This is a condition on directed output dependencies, separate from
bipartiteness of the undirected operand graph. A candidate outside both
positive criteria must have an odd operand cycle and a nonempty positive
memory relation. To avoid a complement collision it must additionally
have alpha zero in every finite 2-group quotient; none of these necessary
filters alone supplies injectivity.

## Spatial target triangles with three colors

For the general quadratic rule (13), form the graph whose edges make
every triple {g,ga_i,gb_i} a triangle. Suppose this graph has a proper
3-coloring. Then injectivity of F implies surjectivity. This is a
different condition from bipartiteness of the operand graph, and can
hold when that operand graph has odd cycles.

Use the compact invariant subshift of all such proper colorings and
hold a coloring fixed throughout. Its three coordinate blocks satisfy

    F_0=x_0+B_0(x_1,x_2),
    F_1=x_1+B_1(x_2,x_0),
    F_2=x_2+B_2(x_0,x_1).

Each B_i is local and bilinear. Make the local reversible input shear

    x_0=z_0-B_0(x_1,x_2).

The transformed first output is z_0. On its zero fiber the second
output is x_1-B_1(x_2,B_0(x_1,x_2)), homogeneous linear in x_1 for
fixed x_2. Both axes are fixed. The finite-x_2 perturbation argument,
followed by the finite-x_1 argument using the uniformly local inverse,
is exactly the two-block proof above and makes this zero fiber
bijective. All intermediate maps are taken over the compact coloring
subshift, so their equivariant inverses have uniform finite memory.

For finitely supported z_0, the transformed map on the remaining two
blocks differs from the bijective zero-z_0 fiber at only finitely many
output coordinates. Its injectivity therefore makes it bijective by
finite coordinate-fiber counting. Density and compactness handle every
z_0. Undo the input shear to obtain surjectivity of F. As in the binary
coloring proof, the coloring itself is never finitely modified.

An exact scope control is the disjoint-pair rule on C_3 times Z,
with t of order three and s generating Z,

    F(x)=x+(R_t x)(R_(t^2) x)
          +(R_(st) x)(R_(st^2) x).                       (16)

Its four operand addresses are distinct and different from 1. Coloring
t^i s^n by i modulo three properly colors all target triangles, while
the operand graph contains triangles on the t-cosets. It also has a
positive memory relation t^3=1, and its alpha=(1+s)(t+t^2) vanishes in
every finite 2-group quotient because t has trivial image there.

Passing those earlier filters does not give injectivity. In fact (16)
has this explicit collision: the t-triples of x alternate 000,100 at
even and odd s-levels, while those of x' alternate 011,111. Put
Q(X)_i=X_(i+1)X_(i+2), with indices modulo three. Then

    Q(000)=Q(100)=000,   Q(011)=100,   Q(111)=111.

At each level F adds Q of that level and of the next. Therefore both
x and x' have output alternating 000,100. This is an exact periodic
collision in a family satisfying the new 3-color criterion, rather
than evidence for an injective nonsurjective rule.

## Single-subgroup masks force both cross-ratio inclusions

For the disjoint-pair rule (14), set A=<a,b> and B=<c,d>. Injectivity
requires both

    a^-1 b in B,   c^-1 d in A.                           (17)

Indeed, on the configuration 1_A the first quadratic term is exactly
1_A and cancels the linear term. If c^-1d is outside A, there is no g
for which both gc and gd belong to A, so the second quadratic term is
zero. Thus F(1_A)=0=F(0), an exact collision. Interchanging the pairs
proves the other inclusion. No finiteness of A or B is needed: subgroup
indicators are valid full-shift configurations.

This completely classifies the natural pair of order-three orbit terms.
If s,t have order three, consider

    F(x)=x+(R_s x)(R_(s^2) x)+(R_t x)(R_(t^2) x).

When <s>=<t>, the quadratic terms coincide and cancel, giving identity.
Otherwise the two order-three subgroups intersect trivially, and
F(1_<s>)=0=F(0) is a three-particle collision. The four operands are
then pairwise distinct. Such a rule cannot be rescued by adding mixed
relations between the actors while keeping their order-three subgroups
distinct. In the general case, satisfying (17) remains only a necessary
condition and supplies no injectivity claim.

## Complete tests for zero and one subgroup-mask collisions

The subgroup restriction also gives an exact classification for the
two input forms 1_H versus 0, and 1+1_H versus 1. This does not classify
arbitrary coset masks or arbitrary collisions.

On right-H-invariant inputs, two shifted coordinates R_s x and R_t x
agree whenever sH=tH. In particular R_s 1_H is the indicator of
H s^-1; two such right cosets are equal or disjoint. It follows that
F(1_H)=0 holds exactly when one quadratic pair has both addresses in H
and the other pair has distinct H-cosets. Existence of a collision of
this zero-mask form is therefore detected completely by failure of
one of the two cross-inclusion tests (17).

For the complemented mask, expand

    F(1+1_H)+1=1_H+(R_a+R_b+R_c+R_d)1_H
                    +(R_a 1_H)(R_b 1_H)
                    +(R_c 1_H)(R_d 1_H).

Within each operand pair, the three terms contribute one coset if
the two addresses have the same H-coset, and two cosets otherwise.
Cancellation with 1_H is possible exactly when one operand belongs
to H and the other three occupy one common coset different from H.
Writing the two surviving values as X=x and Y=R_t x, the restricted
rule is X+XY+Y, Boolean OR. The inputs 1 and 1+1_H then collide.

There are exactly four minimal subgroup tests for this OR pattern:

    b in <a,b^-1c,b^-1d>,
    a in <b,a^-1c,a^-1d>,
    d in <c,d^-1a,d^-1b>,
    c in <d,c^-1a,c^-1b>.                               (18)

Injectivity requires all four memberships. For example, failure of
the first uses H=<a,b^-1c,b^-1d>: the sole operand a lies in H and
bH=cH=dH differs from H. Conversely, any H producing that OR pattern
contains this minimal subgroup while excluding b, so the first test
must fail. The other choices of the sole operand give the remaining
three tests. Together, (17) and (18) completely detect the two specified
subgroup-mask collision forms, and do not assert injectivity when they
all pass.

For an explicit residual family, consider

    F(x)=x+(R_a x)(R_b x)+(R_(ab) x)(R_(ab^2) x).

Both pair-generated subgroups equal <a,b>, so (17) supplies no
obstruction. Nevertheless H=<b> makes the rule on right-H-invariant
data equal to x+(R_a x)x+R_a x, which is OR. If a is outside <b>,
the inputs 1 and 1+1_<b> collide. If a belongs to <b>, all memory
addresses lie in the cyclic subgroup <b>, and the cyclic guard theorem
gives injectivity implies surjectivity. This settles that family for
every order of b, including the odd-order residual cases.

## An A4 collision after a subgroup-linearization test passes

This is a control for the limits of necessary injectivity tests.
The family

    F_(r,t)(x)=x+(R_r x)(R_(rt) x)
                  +(R_(r^2) x)(R_(r^2t) x)               (19)

already has cyclic guard <r>: one operand in each monomial is r or
r^2. Thus injectivity implies surjectivity for every r,t by the guard
theorem above. The following finite control is not an escape from
that theorem.

Let G=A4=N semidirect-product <r>, where N is the Klein four group,
r has order three, and t=rv for a nonidentity v in N. Then t also
has order three. Put e_r=1+R_r+R_(r^2), and similarly define e_t.
On right-<t>-invariant configurations, (19) is the linear map e_r x.
This restricted linear map is injective in this A4 example.

Here is an exact algebraic verification. Work in R=F_2[A4], using
the same e_r,e_t for the corresponding group-ring idempotents. The
kernel J of R -> F_2[A4/N] has J^3=0: the augmentation ideal of
F_2[N] is generated by two commuting square-zero elements, and
conjugation by r preserves its powers. In the quotient, e_r and e_t
coincide. Hence

    e_t e_r e_t=e_t+delta,   delta in e_t J e_t,

has inverse e_t+delta+delta^2 in its corner. If e_t x=x and e_r x=0,
this corner inverse forces x=0. This verification concerns the linear
restriction only; the nonlinear map still has the following collision.

Identify N with F_2^2, put v_i=r^i v r^-i, and choose a linear
functional ell with ell(v)=0 and ell(v_1)=ell(v_2)=1. Write elements
of A4 uniquely as n r^i. Let X be the three values on ell(n)=0 and
Y the three values on ell(n)=1. The output triple on the first level is

    (X_0+X_1Y_2+X_2X_0,
     X_1+X_2X_0+X_0Y_1,
     X_2+X_0Y_1+X_1Y_2),

and the second output triple is obtained by interchanging X and Y.
Direct substitution gives

    (X,Y)=(011,000) -> (011,000),
    (X,Y)=(110,101) -> (011,000).

Equivalently, with H=<v>, the input supports are

    S=Hr union Hr^2,
    S'=N union Hr union (N minus H)r^2.

They have sizes four and eight, respectively, and both map to 1_S.
This symbolic calculation uses the normal Klein four structure, not
enumeration. Both inputs already have zero e_r parity on every
r-coset. More generally (19) preserves e_r x whenever r^3=1, since
F=x+(R_r+R_(r^2))(x R_t x). The A4 control shows that an injective
linear restriction and absence of zero collisions in that restriction
do not establish injectivity on the nonlinear zero-parity fiber.

## Guard extensions beyond cyclic subgroups

The [off-guard elimination theorem](gottschalk-off-guard-quadratic-elimination-2026-09-08.md)
requires no group property of H when each quadratic monomial has
exactly one operand in H. A compact space of separately colored
H-cosets permits recipient-block elimination with uniformly local
inverses. For the common-right-factor rule
`x+x_r x_(rt)+x_s x_(st)`, this excludes a strict embedding whenever
any of `<r,s>`, `<r,st>`, `<rt,s>`, `<rt,st>` is proper in `<r,s,t>`.

The [finite-intersection guard theorem](gottschalk-surjunctive-guard-finite-intersection-proof-2026-09-08.md)
now removes the rank restriction entirely: every surjunctive guard
subgroup suffices, without commensuration or amenability. Its proof
uses the finite poset of intersections of the original mask
stabilizers and preserves the same uniform local recovery condition.
Thus free or other known surjunctive guards also exclude a strict
embedding, even when they are nonamenable. The proofs below remain
valid special cases of this stronger theorem.

The [finite coset stratification proof](gottschalk-virtually-abelian-guard-stratification-2026-09-08.md)
extends support-preserving guard arguments to every abelian subgroup,
using finite memory to reduce to a finitely generated guard. Its
[Hirsch-length extension](gottschalk-polycyclic-guard-rank-extension-2026-09-08.md)
covers every locally virtually polycyclic guard. Both proofs explicitly
retain a uniform local inverse radius during coefficient limits and
cancellation; they do not assume arbitrary injective nonuniform maps
over amenable coordinate sets are surjective.
