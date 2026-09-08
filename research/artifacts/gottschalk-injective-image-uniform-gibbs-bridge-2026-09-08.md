# Injective CA images: uniform Gibbs specification and exact completion counts

Date: 2026-09-08. This verifies a proposed Gibbs bridge for Gottschalk's
conjecture and identifies its remaining boundary obstruction. It proves
neither surjunctivity nor a counterexample. No computation was run.

Let F:A^G -> B^G be an injective finite-memory cellular automaton, where
A,B are finite nonempty alphabets and q=|A|. Put Y=F(A^G). Let sigma:Y -> A^G be
the local inverse, and let M,N be finite memory sets for F,sigma, both
enlarged to contain 1. Let mu be uniform iid on A^G and nu=F_*mu.
The same-alphabet case is B=A, but all the bridge statements below also
hold when the output alphabet is larger.

## The image is an SFT with a unique uniform Gibbs measure

Extend the finite local rule of sigma arbitrarily to patterns outside
its image domain. Then

    Y={y in B^G:F(sigma(y))=y}.

Both inclusions follow from sigma F=Id. The displayed equality is a
finite list of local constraints with memory R=MN (enlarged to contain
1 if necessary), so Y is a shift of finite type.

Fix a finite output set E. A measurable partial bijection within Y that preserves
every coordinate outside E pulls back through F to a partial bijection
of A^G preserving every coordinate outside

    D_E=E N^-1.

Indeed, the local inverse cannot detect the output change at any input
site whose inverse memory misses E. Uniform iid measure is invariant
under every such partial finite-change bijection: condition on all
coordinates outside D_E, where the remaining finite set of input
patterns has equal weights, and use the fiberwise partial bijection.
Therefore nu is invariant under all these output finite-change maps.

For a globally admissible exterior c on G minus E, write

    C_Y(E,c)={p in B^E:p union c belongs to Y},
    N_Y(E,c)=|C_Y(E,c)|.

The invariance just proved implies that the conditional distribution
on this fiber is uniform. More explicitly, for two patterns p,p' in
B^E, the partial replacement p<->p' is defined precisely on exterior
conditions for which both completions are allowed. Invariance equates
their conditional probabilities there. Since B^E is finite, all
allowed completions have equal conditional weights almost surely,
and their probabilities sum to one. Thus

    nu(Y_E=p | Y_(G minus E)=c)=1/N_Y(E,c)

for every allowed p, almost surely in c. Forbidden completions have
probability zero. This is the uniform hard-constraint Gibbs
specification, not merely a statement about typical finite changes.

The specification has no other Gibbs probability measure on Y,
even without assuming shift invariance. If nu' were another, its
pullback by sigma would be invariant under every finite-coordinate
symbol permutation of A^G. The conjugated permutation on Y changes
only finitely many output coordinates and preserves each corresponding
exterior fiber, whose Gibbs distribution is uniform. Every finite
input marginal of the pullback is therefore uniform, so the pullback
is mu and nu'=nu.

This uniqueness is unconditional for the unpinned specification. It
does not assert uniqueness or uniform mixing after arbitrary extra
pinning constraints are introduced.

## The Gibbs conditional depends on a finite collar

For an SFT constraint memory R, every constraint affected by a change
inside E is supported in E R^-1 R. Consequently the allowed set of
completions depends only on the finite exterior collar

    C_E=(E R^-1 R) minus E.

Constraints disjoint from E are already satisfied by any globally
admissible exterior. This gives a finite-boundary version of the
uniform specification for all globally admissible boundary patterns.
The measure nu has full topological support on Y, since F is a
homeomorphism from the full shift onto Y and mu has full support.

## Exact finite-range weak mixing gives a completion-count ratio

The process nu is finitely dependent. Output coordinates in a set U
depend only on source coordinates in UM. In particular, if finite
V lies sufficiently far inside E in the precise sense

    V M M^-1 subset E,                               (1)

then VM and (G minus E)M are disjoint. Source independence implies
that Y_V is independent of all exterior coordinates Y_(G minus E).
Combining this with the Gibbs specification gives

    |{p in C_Y(E,c):p|_V=v}| / N_Y(E,c)
      =nu(Y_V=v)                                    (2)

for almost every exterior c. In fact (2) holds for EVERY globally
admissible exterior c. Both sides on the left are determined by the
finite collar C_E. If (2) failed on any admissible collar pattern,
full support would give that pattern positive probability, contrary
to the almost-sure identity.

This is an exact finite-range weak-mixing statement: the entire
conditioned exterior lies beyond the dependence range of V. It
does not compare two boundaries that differ far away while sharing
arbitrary fixed sites close to V. Such shared pins can transmit
conditional dependence, as the parity-recoding/erasure controls in
`research/artifacts/gottschalk-information-transport-pinning-control-2026-09-08.md`
demonstrate. No strong spatial mixing conclusion is drawn.

## Pointwise divisibility of finite completion counts

Define the free input interior

    I_E={g in G:g M^-1 subset E}.

Since 1 belongs to M,N, we have I_E subset E subset D_E, so these
are finite sets. For every globally admissible exterior c,

    N_Y(E,c)=q^(|I_E|) b_E(c)                        (3)

for a positive integer b_E(c).

To prove this, choose any completion y in Y of c and put x=sigma(y).
All other completions have preimages agreeing with x outside D_E.
Conversely, their preimages are exactly those assignments on D_E
whose F-output agrees with c outside E. The latter constraints do
not involve any coordinate in I_E: changing a coordinate g can
affect outputs only in g M^-1, and this lies inside E for g in I_E.
Thus the allowed preimage set factors exactly as

    A^(I_E) times B_E(c),

where B_E(c) is a nonempty set of assignments on D_E minus I_E.
Input coordinates outside D_E are determined by c through sigma,
so this set does not depend on the initially chosen completion y.
The bijection F between this finite set and C_Y(E,c) proves (3),
with b_E(c)=|B_E(c)|.

In particular,

    q^(|I_E|) <= N_Y(E,c) <= |B|^(|E|),
    H_nu(Y_E | Y_(G minus E))
      =|I_E| log q + E log b_E(Y_(G minus E)).        (4)

The residual integer b_E counts actual input-boundary constraints.
It has not been replaced by a constant or assigned an unproved
entropy sign.

## A literal proper-image control

On G=Z, take binary iid input and the overlapping-pair encoding

    F(x)(n)=(x(n),x(n+1)).

The decoder is projection onto the first coordinate. The output
alphabet has four symbols. The image is the proper SFT specified by
second(y(n))=first(y(n+1)). Its measure is finitely dependent and is
the unique uniform Gibbs measure described above.

For E={1,...,n}, fixing the admissible exterior fixes x(1) and x(n+1),
while x(2),...,x(n) remain free. Hence, for every admissible exterior,

    N_Y(E,c)=2^(n-1).

In particular a one-site output fiber has exactly one completion,
despite the iid source bit and the immediate local decoder. Formula
(3) is exact here with |I_E|=n-1 and b_E=1. The deep-interior count
ratio (2) also holds. Thus Gibbs uniqueness, finite dependence,
pointwise divisibility, and finite-range weak mixing do coexist with
a proper locally conjugate image.

This control changes the alphabet. It does not provide a counterexample
in the same-alphabet case, where a strict image would resolve the
headline problem negatively.

## The precise remaining obstruction

When B=A, (3)-(4) still lose the boundary: the number of free source
coordinates is |I_E| rather than |E|. On a general nonamenable group
there is no argument here making this loss negligible. The exact
ratio (2) redistributes already admissible patterns uniformly over
boundaries; it cannot turn a forbidden pattern into an admissible one.

The same issue appears in the standard proof that reversible CA
preserve uniform measure: it compares preimage counts by replacing
one arbitrary output pattern by another, then applying the inverse.
That replacement is valid on the full shift. For an injective map
onto Y it may leave Y, where the extended inverse is not an inverse.
See Theorem 3 and Corollary 5 of
[Capobianco, Kari and Taati, Post-surjectivity and balancedness of cellular automata over groups](https://arxiv.org/pdf/1507.02472).

Accordingly the Gibbs bridge is proved, including its exact count
consequences, but no boundary-free rank or entropy obstruction at
equal alphabet has been established. Claiming uniform iid output
from injectivity at this point would reintroduce Gottschalk itself
as an unproved step.
