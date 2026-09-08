# Exact collision criterion from the derivative of x R_t x

Date: 2026-09-08. This note gives a necessary and sufficient criterion
for a prescribed difference of the Boolean map Q_t(x)=x R_t x,
and therefore an exact collision criterion for any linear cellular
automaton applied to that quadratic term and added to the input.
The common-factor rule is included. It does not prove that an admissible nonzero
witness exists. No injectivity, counterexample, novelty, or solution
of Gottschalk's conjecture is claimed. No computation was used.

Throughout, G is any group, R_a x(g)=x(ga), T=R_t, and configurations
take values in F_2. The element t may have any finite order, including
one or two, or infinite order.

## Prescribed quadratic differences

Fix configurations delta,q in F_2^G. There exists x such that

    Q_t(x+delta)+Q_t(x)=q                              (1)

if and only if all three conditions below hold.

1. At every g with delta(g)=delta(gt)=0, one has q(g)=0.
2. At every g with delta(g)=0 and
   delta(gt^-1)=delta(gt)=1, one has q(gt^-1)=q(g).
3. On every finite right t-orbit O on which delta is identically 1,
   one has

       sum_(g in O) q(g) = |O| modulo 2.               (2)

There is no parity condition on infinite orbits. Orbits on which delta
is not identically 1 require only conditions 1 and 2.

## Necessity

Write x_i=x(gt^i), delta_i=delta(gt^i), and q_i=q(gt^i) on one
right t-orbit, with indices cyclic when the orbit is finite. Expanding
the product in F_2 gives

    q_i=delta_i x_(i+1)+delta_(i+1) x_i
        +delta_i delta_(i+1).                         (3)

When both delta values on an edge are zero, (3) gives condition 1.
If delta_i=0 and its two neighbors have delta=1, the equations on
the preceding and following edges both give the same value x_i:

    q_(i-1)=x_i=q_i.

This is condition 2, also when the two neighbors are the same vertex
on an orbit of length two. Finally, on a finite orbit with delta=1
everywhere, equation (3) becomes q_i=x_i+x_(i+1)+1. Summing over
the orbit cancels each x_i twice and gives condition 3.

## Sufficiency

Work independently on each right t-orbit. First assign x at vertices
where delta=0. If such a vertex has a neighboring vertex with delta=1,
the intervening edge equation determines x at the zero vertex to
be that edge's q value. If there are two such neighbors, condition 2
says the two prescriptions agree. If there is no such neighbor,
choose x there arbitrarily. Edges with delta=0 at both ends are
already satisfied by condition 1. Thus every edge touching a zero
vertex is handled without constraining x at a delta=1 vertex.

The remaining equations concern edges with delta=1 at both ends:

    x_i+x_(i+1)=q_i+1.                                (4)

On each connected run of delta=1 vertices that is a path, choose
one x value arbitrarily and propagate (4) along the path. This works
for finite paths, either type of one-sided infinite path, and a
two-sided infinite path; in the last case propagate in both directions
from any chosen vertex. No extra consistency condition arises.

The only remaining components are full finite orbits with delta=1
everywhere. Propagating once around such an orbit returns consistently
to the starting value exactly when the sum of q_i+1 is zero. This
is condition 3. Performing these choices on all orbits constructs
x satisfying (1), proving sufficiency.

## The short orbits are included

For t=1, Q_t(x)=x^2=x, so (1) is exactly q=delta. The criterion gives
the same answer: condition 1 forces q=0 where delta=0, while the
one-point instance of condition 3 forces q=1 where delta=1.

For t of order two, the two directed edges describe the same
quadratic product. The criterion handles this duplication. If delta
is 00 on an orbit, it requires q=00. If delta is 10 or 01,
condition 2 requires the two q values to agree, and that equality
is sufficient. If delta is 11, condition 3 again requires the two
q values to agree. Equivalently, the two parallel equations in
(4) are consistent precisely under that condition.

If t has infinite order, every orbit is a two-sided line. Even when
delta=1 on the whole line, recurrence (4) can be solved in both
directions. There is no missing condition at infinity.

## Exact collision criterion for arbitrary linear feedback

Let A be any F_2-linear cellular automaton on F_2^G, and set

    F(x)=x+A Q_t(x).

Then F is noninjective if and only if there is a configuration q for
which

    delta=Aq is nonzero                               (5)

and the pair (delta,q) satisfies conditions 1-3 above.

For necessity, take distinct inputs x,y with F(x)=F(y), and put
delta=x+y and q=Q_t(x)+Q_t(y). Equality of the outputs gives
delta=Aq, and the preceding theorem gives conditions 1-3.

Conversely, suppose q satisfies (5) and the three conditions. The
theorem produces x with Q_t(x+delta)+Q_t(x)=q. Then

    F(x+delta)+F(x)=delta+Aq=0.

Since delta is nonzero, x and x+delta form a collision. This proves
the equivalence. In particular, an arbitrary nonzero q is not a
witness: its transported difference Aq must satisfy all three
conditions, including the finite-orbit parity constraint.

The common-factor rule is the special case A=R_s+R_r. The proof
used only linearity of A, so no restriction on the number or pattern
of its memory addresses is required.

## A finite local constraint formulation

For fixed A and t, all conditions on q above are given by finitely
many forbidden local patterns. Conditions 1 and 2 involve only the
finite memory of A and its t-translates. If t has finite order n,
condition 3 is also local: on the finite orbit g<t>, when all delta
values are one, require the sum of q to equal n modulo two. If t
has infinite order, this extra condition is absent.

Thus F is noninjective exactly when this binary subshift of finite
type has a point q with (Aq)(1)=1. The pin at the identity loses no
witness: any nonzero delta can be translated to put a one there.
The theorem reconstructs a collision from any such global q using
the orbit recurrences. Satisfying one finite collection of these
constraints alone does not certify a global witness.

## A precise obstruction to a single subgroup mask

In this section take A=R_s+R_r.

Suppose K is a subgroup with t,t^2 outside K, and let q=1_K. Suppose
also that

    R_s q=T^-1q,       R_r q=Tq.                       (6)

Then no collision of F can have the prescribed quadratic difference
Q_t(x)+Q_t(y)=q.

Indeed, such a collision would require

    delta=(R_s+R_r)q=T^-1q+Tq.

At the identity, q(1)=1 and q(t^j)=0 for j in {-2,-1,1,2}; the
negative exclusions follow because K is a subgroup. Therefore

    delta(1)=0,       delta(t^-1)=delta(t)=1,
    q(t^-1)=0,        q(1)=1.

Condition 2 would require q(t^-1)=q(1), a contradiction. The same
obstruction can be read at the middle zero between the two nonzero
values of delta: the adjacent quadratic differences must agree,
whereas the proposed mask assigns them unequal values.

This applies to the remaining conjugacy case in the
[Tarski operand-reversal artifact](gottschalk-tarski-operand-reversal-exclusions-2026-09-08.md)
after imposing its classification also on the reversed operands.
Here is that implication explicitly. A surviving conjugacy case has

    r^-1tr in <s>,       s^-1ts in <r>.

The reversed classification, after conjugating its subgroups by t,
requires either

    t^-1r in <ts>,       t^-1s in <tr>,                (7)

or r^-1tr in <ts> and s^-1ts in <tr>. The latter alternative is
impossible: the nonidentity element r^-1tr would belong to both
<s> and <ts>, which are distinct order-p subgroups because s,t do
not commute. Thus (7) is necessary for any surviving strict candidate.

Take K=<ts>. Noncommutation gives t outside K, and odd prime order
also gives t^2 outside K. Since R_(ts)q=q, one has R_s q=T^-1q.
The first membership in (7) gives R_r q=Tq. Hence (6) holds and the
single-mask obstruction applies.

This rules out only that prescribed q. It neither proves injectivity
of the remaining rule nor rules out admissible witnesses built from
multiple masks or other configurations. Existence of a nonzero q
satisfying the full criterion is the remaining nonlinear question.
