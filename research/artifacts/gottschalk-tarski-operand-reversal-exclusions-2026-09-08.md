# Operand reversal excludes two Tarski common-factor branches

Date: 2026-09-08. This note proves two exclusions for injective
nonsurjective cellular automata within the common-factor family.
Some cases use a cyclic guard, so the conclusion is a strict-candidate
exclusion rather than a claim that every rule in those cases is
noninjective. No novelty claim or solution of Gottschalk's conjecture
is asserted. No computation was used.

## Setting and previously established inputs

Let G be an infinite group of exponent p, where p>=5 is prime, whose
nontrivial proper subgroups all have order p. Fix noncommuting s,t.
Existence for sufficiently large primes, with an original literature
source, is recorded in the
[Tarski control artifact](gottschalk-tarski-common-factor-residual-controls-2026-09-08.md).
The proof here is conditional on the stated group properties.

Use R_a x(g)=x(ga), T=R_t, and Q_t(x)=xTx over F_2. Put

    r=us,   H=<s>,   A=t^2s,   B=s^-1ts,
    C={v : v^-1tv is in H}.

The rule is

    F(x)=x+(1+R_u)R_s Q_t(x)
        =x+(R_s+R_r)Q_t(x).                            (1)

Distinct subgroups of order p intersect trivially. The normalizer
of any such subgroup J is J itself. Indeed, a larger normalizer
would be G; conjugation on J would be trivial since G has exponent
p and Aut(C_p) has order p-1. Then J would be central, and together
with an element outside J would generate a subgroup of order p^2,
contradicting the assumed subgroup property.

In particular s is outside <t>, t is outside H, and the subgroups
H and <t> intersect trivially. Both A and B are nonidentity and lie
outside H: membership of A would put t^2 and hence t in H;
membership of B would also put t in H. Thus <A> and <B> each meet
H trivially. The elements st and ts are nonidentity, since otherwise
s,t would commute.

We use the five-exclusion witness and cyclic-guard theorem proved in
the [common-factor collision artifact](gottschalk-common-factor-coset-collisions-2026-09-08.md).
In the notation F=x+(1+R_v)R_a Q_b(x), the witness uses q=1_<a>:

    b,b^2,v,b^2v,v^-1bv all outside <a>

give distinct inputs q+R_(b^-1)q and R_(b^-1)q+R_vq with the same
image. A cyclic subgroup containing one operand from each quadratic
monomial instead gives injectivity implies surjectivity by guard
transfer.

The cited artifact reduces any strict candidate in the present
Tarski setting to four necessary cases, expressed using r:

    r in t^-2H intersect <A>,    r in t^-2H intersect <B>,
    r in C intersect <A>,        r in C intersect <B>.   (2)

The equivalence between u in C and r=us in C follows because C is
stable under right multiplication by H. If C is nonempty, it is a
single coset v_0H, as proved in the cited artifact.

## Exact operand reversal

Pointwise multiplication gives

    Q_t(x)=T Q_(t^-1)(x).

Consequently the same rule admits both descriptions

    F=x+(1+R_u)R_(st)Q_(t^-1),
    F=x+(1+R_(u^-1))R_(rt)Q_(t^-1).                   (3)

These are identities of the original map, not a change in its
injectivity or surjectivity problem. The second identity also swaps
the two quadratic terms.

## Exclusion of r in C intersect <A>

Assume r is in C intersect <A>, so u=rs^-1 is in C. Put J=<st>.
The element t lies outside J: otherwise J=<t>, and
s=(st)t^-1 would lie in <t>. Thus t^-1 and t^-2 also lie outside
J. Moreover J is distinct from H, since st in H would imply t in H.

If u lies in J, then both st and rt=u(st) lie in J. They provide
a cyclic guard for the two quadratic terms, proving injectivity
implies surjectivity. Hence suppose u is outside J and use the
first reversed description in (3).

The conjugation exclusion holds: u^-1t^-1u is a nonidentity element
of H because u is in C, and H intersect J={1}.

It remains to show that t^-2u is outside J. Suppose instead that
b=t^-2u is in J. Then

    r=us=t^2bs=A(s^-1bs).

Since A,r lie in <A>, this puts s^-1bs in <A>. But b in <st> puts
s^-1bs in <ts>. The subgroups <A> and <ts> are distinct: if they
were equal, A(ts)^-1=t would lie in that subgroup, and then so
would s=t^-1(ts), contradicting noncommutation. Their intersection
is therefore trivial. It follows that b=1 and u=t^2. This contradicts
u being in C, since (t^2)^-1t(t^2)=t is outside H.

All five exclusions now hold for (a,b,v)=(st,t^-1,u). With q=1_J,
the explicit inputs

    x=q+Tq,       y=Tq+R_uq

are distinct and satisfy F(x)=y=F(y). Thus every rule in this branch
either has this collision or is excluded by the cyclic guard J.

## Exclusion of r in t^-2H intersect <B>

Assume r is in t^-2H intersect <B>. Write r=t^-2v with v in H,
and put J=<rt>. The element r is nonidentity, since otherwise
t^2 would lie in H. Thus <r>=<B>.

The subgroups <B> and <t> are distinct: equality would make s
normalize <t>, forcing s into <t>. It follows that r is outside
<t>, so rt is nonidentity. Also t is outside J. Otherwise r=(rt)t^-1
would be in J, making J=<r>=<B>, while t in J would make J=<t>.
The same argument shows B is outside J: membership of B would put
r in J, hence t=r^-1(rt) in J. In particular t^-1,t^-2 are outside J.

If u^-1 is in J, then rt and st=u^-1(rt) both lie in J and give
a cyclic guard. Otherwise use the second reversed description
in (3), with (a,b,v)=(rt,t^-1,u^-1).

Its conjugation exclusion holds because

    u t^-1u^-1=rB^-1r^-1=B^-1,

and B is outside J. Here r commutes with B because r is in <B>.

For the last exclusion, put E=t^-2st. Then

    t^-2u^-1=E(rt)^-1,

so it suffices to prove E is outside J. First, v is not s. If it
were, r=t^-2s and conjugation by s would give sr s^-1=st^-2 in
<t>, since r is in <s^-1ts>; this would put s in <t>.

Suppose now that E is in J. Both rt=t^-2vt and E are in J, so

    (rt)^-1E=t^-1v^-1st

is in J. It is a nonidentity element of t^-1Ht, since v!=s.
Both J and t^-1Ht have order p, hence they are equal. Conjugating
rt in J by t then gives tr in H. But t^2r=v is also in H, implying

    (t^2r)(tr)^-1=t in H,

a contradiction. Thus E and t^-2u^-1 lie outside J.

All five exclusions hold. With q=1_J, the explicit inputs

    x=q+Tq,       y=Tq+R_(u^-1)q

are distinct and satisfy F(x)=y=F(y). This branch is therefore also
excluded, either by the collision or by the cyclic guard J.

## The two remaining exact cases

Combining the preceding exclusions with (2), any strict candidate
must satisfy one of

    r in t^-2H intersect <t^2s>,
    r in C intersect <s^-1ts>,       u=rs^-1.           (4)

Each intersection has at most one element. Indeed, <A> and <B>
meet H trivially, and a coset gH meets either subgroup in at most
one point: the ratio of two common points would belong to both
H and that subgroup. This applies to C because it is empty or a
single coset of H. Thus at most two actors u remain for the fixed
noncommuting s,t.

These are necessary parameter relations for cases not excluded by
the proved mechanisms. Neither existence of such an intersection
nor injectivity of its rule is asserted, and the remaining cases
are not claimed to produce a counterexample.
