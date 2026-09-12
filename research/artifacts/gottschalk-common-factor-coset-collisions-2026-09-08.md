# Coset collisions and elimination when the outer actor is a power

Date: 2026-09-08. For every group G and s,t,u in G with u in <t>,
the Boolean cellular automaton

    F(x)=x+(1+R_u)R_s(xR_t x)                           (1)

satisfies injectivity implies surjectivity. For general u, an exact
five-exclusion subgroup witness gives a broad class of collisions.
These results exclude construction families; they do not solve
Gottschalk's conjecture or assert injectivity of any residual rule.
No computation was used.

The later [operand-reversal proof](gottschalk-tarski-operand-reversal-exclusions-2026-09-08.md)
excludes two of the four final Tarski cases below, leaving at most two
actors for fixed noncommuting s,t. No injectivity claim is made for
either remaining case.

Write R_a x(g)=x(ga), T=R_t, U=R_s, V=R_u, and Q(x)=xTx.
Thus R_a R_b=R_(ab). The expanded quadratic operands in (1) are
(us,ust,s,st). Coincident addresses are allowed.

## The five-exclusion witness

Put H=<s> and q=1_H. Suppose

    t, t^2, u, t^2u, u^-1tu all lie outside H.          (2)

Then the configurations

    x=q+T^-1q,       y=T^-1q+Vq

are distinct and satisfy F(x)=y=F(y).

For precise orientation, R_a q is the indicator of H a^-1.
The supports of R_a q and R_b q are equal exactly when a^-1b is
in H, and otherwise are disjoint. Since t,t^2 are outside H,

    Q(x)=(q+T^-1q)(Tq+q)=q.

Also

    Q(y)=(T^-1q+Vq)(q+TVq)=0.

The four products in the latter expression have disjoint factors
because respectively t, t^2u, u^-1, u^-1tu are outside H.
As Uq=q, we obtain

    F(x)=x+(1+V)q=y,       F(y)=y.

Finally x+y=q+Vq is nonzero because u is outside H.

Condition (2) is exactly equivalent to the three intermediate
properties Q(x)=q, Q(y)=0, and x!=y for this specified witness.
Indeed, Q(x)=q requires t,t^2 outside H: if t is in H then x=0;
if t is outside H but t^2 is in H, then Q(x)=q+Tq rather than q.
Distinctness requires u outside H. Under these three exclusions,
membership of t^2u in H makes T^-1q=TVq, giving a common nonzero
coset in y and Ty which cannot cancel. Membership of u^-1tu in H
similarly makes Vq=TVq and gives a common nonzero coset. Therefore
the last two exclusions are also necessary for Q(y)=0. This exactness
claim concerns these intermediate properties, not all ways in which
the same two configurations, or arbitrary inputs, might collide.

## A second witness for the outer actor t^-2

Suppose u=t^-2, put K=<ts>, and let q=1_K. Then

    TUq=R_(ts)q=q,       Uq=T^-1q.

Let d be the period of the sequence T^i q. Equivalently,
d=[<t>:<t> intersect K], allowing d to be infinite. Distinct shifts
modulo d have disjoint supports.

If d>=5 or d is infinite, put

    z=q+T^-1q+T^-3q.

The shift-index sets {0,-1,-3} and {1,0,-2} have only 0 in common,
also when reduced modulo any finite d>=5. Consequently Q(z)=q,
whereas Q(q)=0. Hence

    F(z)=z+(1+T^-2)T^-1q=q=F(q),       z!=q.            (3)

If d=3, use instead z=q+T^-1q. Then Q(z)=q and T^-3q=q, so

    F(z)=z+(1+T^-2)T^-1q=0=F(0),       z!=0.           (4)

These witnesses use only the stated coset period, with no assumption
that K is normal or that its cosets carry a quotient group structure.

## The complete power-actor theorem

Assume u is in <t>. The memory subgroup is M=<s,t>, and F acts
independently on the cosets gM. Restricting to one such coset and
setting the others to zero shows that injectivity on G implies
injectivity of the same rule on M. Surjectivity on M gives
surjectivity on every coset and hence on G.

If t=1, then u=1 and F is identity. If t has infinite order or
finite even order, the operand graph has edges {h,ht}; each right
t-orbit has a proper alternating coloring. The spatial bipartite
quadratic theorem in the
[block-elimination artifact](gottschalk-quadratic-block-elimination-2026-09-08.md)
therefore gives injectivity implies surjectivity.

Now let t have finite odd order, and suppose F is injective. Set

    N=<t> intersect <s>.

The group N is finite and central in M, since it commutes with both
generators. If u is in N, the cyclic group <s> is a guard: each
quadratic monomial has an operand in <s>, namely us or s. The
[surjunctive-guard transfer theorem](gottschalk-surjunctive-guard-finite-intersection-proof-2026-09-08.md)
gives surjectivity in this case. This branch includes u=1, where F
is identity even when M is nonabelian.

Suppose instead that u is outside N. Pass to M_1=M/N, and denote
the images of s,t,u by s_1,t_1,u_1. The rule on M_1 inherits
injectivity: pullback along the quotient map embeds its full shift
as the subspace of N-invariant configurations on M and intertwines
the two local rules. A collision on the quotient would therefore
be a collision on M.

In M_1, the subgroups <t_1> and <s_1> intersect trivially. To check
this, an equality t^aN=s^bN gives t^a=s^b n for some n in N;
then t^a lies in <t> intersect <s>=N, so the common quotient element
is identity. The element t_1 has nontrivial odd order, and
u_1 is a nonidentity power of t_1.

Apply the first witness on M_1 with H_1=<s_1>. The elements t_1,
t_1^2, and u_1 lie outside H_1. Also u_1^-1 t_1 u_1=t_1.
Unless t_1^2u_1=1, all five exclusions hold and contradict
injectivity. Therefore

    u_1=t_1^-2.

Put K_1=<t_1s_1> and

    d=[<t_1>:<t_1> intersect K_1].

This is an odd positive integer. If d>=5, witness (3) contradicts
injectivity on M_1. If d=3, witness (4) does the same. It follows
that d=1, so t_1 is in K_1, and then s_1=t_1^-1(t_1s_1) is in K_1.
Thus M_1=K_1 is cyclic. It contains the nonidentity finite-order
element t_1, so this cyclic group is finite.

Finally, a central extension of a cyclic group is abelian: choose
a lift a of a cyclic generator of M_1 and write every element of M
as a^j n with n in N; all these elements commute. Since both N
and M_1 are finite, M is finite as well. On the finite configuration
space {0,1}^M, injectivity implies surjectivity by counting.

This completes the proof for all orders of t. The finite-odd part
also proves the precise necessary alternative

    F injective  implies  u in <s> or M=<s,t> finite abelian.

The first alternative cannot be omitted: u=1 gives identity on
every group. No converse injectivity claim is made.

## Conditional control on odd-prime Tarski groups

Let G be an infinite exponent-p Tarski group for a sufficiently large
odd prime p, and fix noncommuting s,t. Existence and its literature
scope are documented with the original source in the
[Tarski control artifact](gottschalk-tarski-common-factor-residual-controls-2026-09-08.md).
Every nontrivial proper subgroup has order p. Put H=<s>.
Then t,t^2 are outside H.

The five-exclusion witness gives a collision for every u outside

    H union t^-2H union C,
    C={u : u^-1tu is in H}.                            (5)

The set C is either empty or one coset u_0H, hence has at most p
elements. Indeed, N_G(H)=H: a larger normalizer would be G, making
H normal, and conjugation would be trivial because G has exponent p
while Aut(C_p) has order p-1. This would make H central, contradicting
the Tarski subgroup property. If u_0 is in C, every other u in C
conjugates <t> onto the same H; hence u_0^-1u normalizes H and lies
in H. Thus (5) has at most 3p elements.

The class u in H is already excluded as a strict candidate by the
cyclic guard H. The power-actor theorem excludes every nonidentity
u in <t>: here <t> intersect H is trivial and <s,t>=G is not finite
abelian, so injectivity is impossible. In particular it excludes
u=t^-2 from the second exceptional class in (5).

Before using the swapped-term witness, the remaining cases lie in

    (t^-2H minus {t^-2}) union C,

a set of at most 2p-1 actors for the fixed s,t. The next refinement
reduces this bound to four. These are bounds on cases not settled by
the displayed witnesses, not assertions of injectivity. Other tests
may exclude them as well.

## The swapped witness and a cyclic mask leave at most four actors

Continue with the fixed noncommuting s,t in the preceding section.
Swapping the two quadratic terms replaces s by r=us and u by u^-1.
Put K=<r> and define the two fixed elements

    A=t^2s,       B=s^-1ts.

Both lie outside H, so <A> and <B> meet H trivially. The last two
exclusions in the swapped witness become

    t^2u^-1 outside K  iff  A outside K;
    utu^-1 outside K  iff  B outside K.                (6)

Here u^-1=sr^-1 and utu^-1=rBr^-1. Membership of both A and B
in K is impossible: it would give K=<B>, and conjugating A by s
would put sAs^-1=st^2 in <t>, contrary to s being outside <t>.

First let u=t^-2h with h in H. Then r=t^-2hs is outside H, and
u is outside K: otherwise s=u^-1r would lie in K, forcing K=H.
Furthermore t lies in K exactly when h=s^-1. Indeed, t in K gives
K=<t>, hence hs=t^2r lies in H intersect <t> and equals 1; the
converse is immediate. For every h other than s^-1, both t and
t^2 lie outside K, so the swapped witness gives a collision unless
A or B lies in K. Such membership forces respectively

    r in t^-2H intersect <A>,
    r in t^-2H intersect <B>.

Each intersection contains at most one element. In general a coset
gH meets a subgroup J with H intersect J={1} in at most one point:
the ratio of two common points would lie in both H and J. Thus at
most three actors from t^-2H survive this pass: u=t^-2s^-1 and at
most one actor from each of the two displayed intersections.

The distinguished actor u=t^-2s^-1 has a further collision. More
generally, suppose r=us lies in J=<t> and s^-1ts lies outside J.
Put q=1_J. Then Tq=q, Q(q)=q, and R_rq=q, giving

    F(q)=q+Uq+R_rq=Uq.

The supports of Uq and TUq are disjoint, by the exact condition
s^-1ts outside J. Thus Q(Uq)=0 and

    F(Uq)=Uq=F(q),       Uq!=q.

For the distinguished Tarski actor, r=t^-2 is in J, and
s^-1ts is outside J because N_G(J)=J and s is outside J. This
uses finiteness of J: a conjugate of its generator lying in J
would conjugate J onto J. Therefore this actor is excluded, and
at most two actors from t^-2H remain.

Next suppose C is nonempty and u is in C. Since C=u_0H and r=us,
r is also in C, so r^-1tr lies in H. It follows that t is outside
K: if t were in <r>, then r^-1tr=t would lie in H. The element u
is outside K by the same argument as above; here r is outside H
because C is disjoint from H. Therefore the swapped witness gives
a collision unless A or B lies in K. These alternatives force

    r in C intersect <A>,       or r in C intersect <B>.

Each intersection again has at most one point. Consequently at most
two actors from C survive. Also C is disjoint from t^-2H: for
u=t^-2h one has u^-1tu=h^-1th outside H.

Together the two classes leave at most four actors for the fixed
s,t, with their exact necessary subgroup relations displayed above.
This finishes the bounded refinement. No injectivity or counterexample
claim is made for these at most four cases.
