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
