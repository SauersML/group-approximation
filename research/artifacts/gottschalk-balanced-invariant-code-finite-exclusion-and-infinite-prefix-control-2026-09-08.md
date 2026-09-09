# Balanced invariant codes: finite exclusion and an infinite countercontrol

Date: 2026-09-08. A nonzero balanced scalar linear feedback on a
finite source group gives a two-track triangular involution that
cannot be encoded into a scalar invariant code by any injective
quadratic intertwiner. The target map need only be equivariant;
neither target injectivity nor zero preservation is required.

The finite proof distinguishes three points by quadratic fiber
sizes. An explicit continuous automorphism on an infinite source
commutes with both the quadratic map and the triangular involution
while moving two of those points. It therefore prevents extending
that particular intrinsic-point argument to infinite sources.
It is not itself a scalarization construction. The subsequent
[infinite-code construction](gottschalk-balanced-triangular-invariant-scalar-code-construction-2026-09-08.md)
combines these maps with component permutations to obtain an
actual continuous Q-encoding with reversible dynamics on a proper
invariant scalar code. Injective or reversible full-shift extension
remains unresolved.

This complements the full-conjugacy, affine-code, and unbalanced
nonlinear-code obstructions in
[the intertwiner artifact](gottschalk-directed-quadratic-intertwiner-rigidity-2026-09-08.md).
No computation is used, and no resolution of Gottschalk's
conjecture is claimed.

## Finite-source invariant-code exclusion

Let G be a finite group, let t have order three, and write

    T=R_t,       Q_t(x)=x(Tx),       E=I+T+T^2.

On the two-track source X=(F_2^G)^2, write Q for the operation
applying Q_t separately to both tracks. Let A be a nonzero scalar
linear G-equivariant map with A1=0, and set

    F_A(x,y)=(x+A Q_t(y),y).

This is an involution. The hypothesis AE != 0 from the balanced
full-conjugacy obstruction implies A != 0, so the present theorem
includes that entire finite-source case.

Suppose a group Lambda acts transitively on the coordinates of
a scalar binary target space Y, commutes with its quadratic map
Q', and preserves a code C contained in Y. There is no injective
map L:X -> Y with image C satisfying

    Q' L=L Q,       F' L=L F_A

for a Lambda-equivariant target map F':Y -> Y. The standard case
is a scalar group shift with Q'=Q_s for an element s of order
three. No continuity or affinity of L is needed, and F' need
not be injective, continuous, or zero-preserving.

### Three intrinsically distinguished points

On a single triple, Q_t^2 sends 111 to 111 and every other
state to 000. Thus im Q^2=Fix Q. A Q-fixed configuration p
with k zero triples has

    |(Q^2)^-1(p)|=7^k.

There are finitely many triples. Among Q-fixed points, (0,0)
is therefore the unique point with largest Q^2-fiber, and
(1,1) is the unique point with smallest Q^2-fiber. Every
automorphism of X commuting with Q fixes both points.

Define a further intrinsic set, explicitly restricted to Fix Q:

    P={p in Fix Q : F_A fixes every point of (Q^2)^-1(p)}.

Then

    P={(m,1): m is constant on every right-t orbit}.

For the inclusion from right to left, the y track of any
preimage must be 1, and A Q_t(1)=A1=0. Conversely, suppose
p=(m,n) has a zero triple in n. Within (Q_t^2)^-1(n), vary
that triple between 000 and a weight-two state whose Q_t-image
is a coordinate unit delta_g, keeping all other triples fixed.
The two A Q_t(y) values differ by A delta_g, which is nonzero.
Indeed scalar equivariance makes all columns of A translates
of one another; if one vanished, all would vanish and A=0.
The two values cannot both be zero, so F_A does not fix the
whole Q^2-fiber. This proves the characterization of P.

Within P, the unique point with largest ambient Q^2-fiber is
(0,1). Consequently every automorphism commuting with both Q
and F_A fixes the three distinct points

    (0,0),       (1,1),       (0,1).

### Contradiction in a scalar invariant code

An asserted encoding L is a bijection from X onto C. Each
lambda in Lambda induces a source automorphism

    H_lambda=L^-1 lambda L.

Code invariance makes this well-defined and bijective. Target
commutation with Q' and the relation Q'L=LQ make H_lambda
commute with Q. Target equivariance and F'L=LF_A make it
commute with F_A. Hence it fixes all three distinguished
points. Their three images under L are distinct configurations
fixed by Lambda. A transitive coordinate action on a scalar
binary space has only two fixed configurations, namely 0 and 1.
This is impossible and proves the theorem.

## A continuous infinite-product countercontrol

The following construction shows why those same three points
cannot simply be declared intrinsically fixed in the infinite
case. Let D be any finite alphabet with maps q,f:D -> D and
a symbol u such that

    q(u)=f(u)=u,       q^-1(u)=f^-1(u)={u}.

The maps q and f need not commute with each other. Apply them
coordinatewise on D^N. Classify a symbol as U if it equals u,
and as Z otherwise. Both maps preserve this classification.

Define H using the following finite prefix substitutions, copying
the values of all Z symbols in order and then copying the entire
remaining suffix:

    UU  -> UU
    UZU -> UZ
    UZZ -> ZZ
    Z   -> ZU.

The source prefixes {UU,UZU,UZZ,Z} are disjoint and complete.
The target prefixes {UU,UZ,ZZ,ZU} are likewise disjoint and
complete. Each substitution preserves the number and order of
Z symbols, so the reverse substitutions recover both their
values and the suffix. These finitely many pieces are clopen;
H and its inverse are continuous.

Since q and f preserve the U/Z masks, applying either map does
not change the selected prefix rule. Copying symbols and
inserting or deleting the fixed symbol u commutes with both
maps. Consequently

    H q=q H,       H f=f H

on the product. For every z != u, however,

    H(z,z,z,...)=(z,u,z,z,...).

Thus a constant non-u configuration need not be fixed by all
continuous automorphisms of the pair of operations.

## Application with a genuinely nonzero off-axis component

Take G_0=A_4, t=(123), and h=(12)(34). On

    G=A_4 x Z,       A=I+R_h,

both Q and F_A act independently on the A_4-indexed components.
Each component alphabet is D=(F_2^{A_4})^2. Set u=(1,1) in D.
It is fixed by Q and has a singleton Q-preimage. Also A1=0,
so F_A fixes u; since F_A is an involution, its preimage of
u is a singleton as well. Enumerate the Z-indexed components
by N and apply the prefix construction. This reindexing does
not affect either componentwise operation.

This example has the requested nonzero off-axis component.
In F_2[A_4], write e=1+t+t^2. Then

    (1-e)(1+h)e=(t+t^2)h(1+t+t^2) != 0.

The six displayed group elements are distinct: an intersection
between the sets t h<t> and t^2 h<t> would force h^-1 t h
to lie in <t>. But h^-1 t h=(214), which is outside <(123)>.
Thus no coefficient cancellation occurs. Equivalently,
(I-E)AE is nonzero as a scalar linear cellular automaton.

The continuous homeomorphism H commutes with Q and F_A but
moves the global all-zero configuration and the global (0,1)
configuration, inserting a component u into each. Hence neither
point is characterized as fixed by all continuous automorphisms
of this infinite pair, even with (I-E)AE != 0.

The prefix homeomorphism is not G-equivariant: it sends a constant
configuration to a nonconstant one. It is an automorphism of the
two operations, not a claimed scalar cellular automaton. Likewise,
an arbitrary code encoding need not conjugate target shifts to
source-G-equivariant maps, so source equivariance cannot be silently
added to the intrinsic-point argument.

The prefix homeomorphism alone is a countercontrol to extending
the finite fiber-extremum proof. The subsequent
[orbit construction](gottschalk-balanced-triangular-invariant-scalar-code-construction-2026-09-08.md)
does provide a continuous injective Q-encoding with reversible
dynamics on an invariant scalar code. The remaining issue is an
injective or reversible ambient full-shift extension, particularly
one in the scalar linear-feedback family x+B Q_s.
