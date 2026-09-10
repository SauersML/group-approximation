# Finite fibers, compression, and the remaining index question

September 10, 2026. Written deductions from complete-section induction
and the finite-index relative-cost repair already recorded in Cairn.
No mathematical priority, independent verification, or universal Fixed
Price proof is claimed. In particular, the equivalence below does not
assert either of its two universal propositions.

## 1. A uniform finite-fiber bound

Let pi:Y->X be an equivariant p.m.p. factor between essentially free
actions of a countably infinite group Gamma. Assume each fiber has
q points with uniform conditional measure 1/q, for one fixed integer
q>=1, on the chosen conull standard Borel models.

Then, with the usual extended-real interpretation,

    C(Y)<=C(X)<=1+q(C(Y)-1).                                 (1)

Choose a measurable enumeration of each finite fiber and identify Y
as a probability space with X x {1,...,q}, with product uniform
fiber measure. The action permutes these labels by a measurable
cocycle; no invariant enumeration or measurable equivariant section
is assumed.

Let S be the orbit relation on Y. Enlarge it to

    T={(y,y'): pi(y) R_X pi(y')}.

Under the chosen enumeration, T is R_X times the full relation on
{1,...,q}; in particular it is p.m.p. Freeness of the base action
implies that each S-class meets each fiber above its projected orbit
in exactly one point. Each T-class consequently consists of exactly
q S-classes. The established finite-index relative-cost repair gives

    C(T)<=C(S)=C(Y).                                       (2)

For finite C(S), append relative repairs of arbitrarily small cost
to near-optimal S-graphings. If C(S)=infinity, (2) is automatic.
The section X x {1} is T-complete, has measure 1/q, and carries
R_X with normalized measure mu. Complete-section induction gives

    C(T)-1=(C(X)-1)/q.                                    (3)

Equations (2)--(3) prove the upper bound in (1); lifting base
graphings proves the lower bound. This uses a compression identity
for T, not a cost-multiplication identity for S contained in T.

In particular, C(Y)<infinity forces C(X)<infinity, and C(Y)=1
forces C(X)=1. Thus this uniform finite-fiber setting cannot exhibit
a finite-cost source over an infinite-cost base. For costs above
one the estimate does not give equality.

### Atomic conditional measures over an ergodic base

There is a further consequence without a finite-fiber hypothesis.
Suppose the base action on X is ergodic and the conditional measures
nu_x have atoms. Equivariance of disintegration makes the largest
atom mass a(x) and the number q(x) of atoms of that mass invariant
functions on X. Ergodicity makes them constants a>0 and q<infinity
almost everywhere. The largest mass is attained: a summable list
of positive masses with positive supremum has a maximum. These
functions and their atom sets are measurable for a probability
kernel on standard Borel spaces.

Let A be the set of points y whose conditional atom has that largest
mass. Then A is Gamma-invariant and has measure m=qa>0. With its
normalized measure, A projects to X as a uniform q-point factor:
the conditional mass of A is the same m at almost every x, and
each of its q points has normalized conditional mass 1/q.

Apply (1) to this factor. Additivity of cost across the invariant
partition A and its complement, and the aperiodic lower bound on
the complement when it is nonnull, give

    C(X)-1 <= q(C(A,nu_A)-1),
    C(Y)-1 >= m(C(A,nu_A)-1).

The additivity used here follows by restricting every graphing to
the two invariant pieces for one inequality and combining their
near-optimal graphings for the other. For finite C(Y), combining
the inequalities gives

    C(X)-1 <= (C(Y)-1)/a.                                 (1a)

If C(Y)=infinity, this inequality is automatic. Thus a finite-cost
free source over an ergodic infinite-cost free base must have
nonatomic conditional measures. The conditional measures need not
be purely atomic or have equal atom weights for this consequence:
any positive atomic part is enough over an ergodic
base. It also proves descent of cost one in this atomic setting.
There is no lower bound on a for a diffuse extension, and no
ergodicity-free uniform bound is claimed when a(x) varies.

## 2. Finite fibers encode the finite-index question

For either the class of all countably infinite groups or the class
of all infinite finitely generated groups, consider two assertions:

* (F) Every free p.m.p. factor with uniform constant finite fibers
  preserves action cost.
* (I) For every free p.m.p. Gamma-action a and finite-index subgroup
  H<=Gamma, one has

      C(a restricted to H)-1=[Gamma:H](C(a)-1).

Then (F) and (I) are equivalent. They are conditional assertions
here. The cost of a specified action in (I) must not be replaced by
the infimum of costs over all actions of the group.

### (F) implies (I)

Use left actions in this note. Given H<=Gamma of index q and a on
X, let Gamma act diagonally on

    Y=X x Gamma/H

with uniform coset measure. Its projection onto X is a uniform
q-point free extension. The section A=X x {H} is complete for
the Gamma-action on Y, has measure 1/q, and its restricted relation
is exactly the H-action on X. Therefore induction gives

    C(Y)-1=(C(a restricted to H)-1)/q.                      (4)

If (F) holds, C(Y)=C(a), so (4) proves (I).

### (I) implies (F)

Represent the given q-point extension as Y=X x {1,...,q}, with

    gamma.(x,i)=(gamma.x, sigma(gamma,x)i),

where sigma is a measurable cocycle into P=Sym(q). Let H<=P be
the stabilizer of 1, of order (q-1)!. On Z=X x P, with uniform
P-measure, define the action of L=Gamma x P by

    (gamma,k).(x,u)=(gamma.x, sigma(gamma,x)u k^(-1)).

The cocycle identity verifies the action law. It is p.m.p., and it
is free: a fixed point forces gamma=e by base freeness and then
k=e by the free right P-action. Let L'=Gamma x H, of index q.

Quotienting the finite right P-orbits recovers X, and quotienting
the finite right H-orbits recovers Y via (x,u)->(x,u(1)). Choose
measurable transversals of these finite orbits. They are complete
sections for the L- and L'-relations, respectively. Their measures
are 1/|P| and 1/|H|. With normalized measure, their restricted
relations are R_X and R_Y. Hence induction gives

    C(L acting on Z)-1=(C(X)-1)/|P|,
    C(L' acting on Z)-1=(C(Y)-1)/|H|.                       (5)

Apply (I) to L'<=L in this specific free action. Since |P|=q|H|,
equations (5) give C(Y)-1=C(X)-1, proving (F). The auxiliary groups
are still countably infinite, and still finitely generated when
Gamma is. Thus both stated choices of scope are preserved.

## 3. What the equivalence prevents us from assuming

The finite-index equality for specified free actions is the question
recorded by [Furman, A Survey of Measured Group Theory, Question 4.11](https://math.uchicago.edu/~shmuel/L%5E2%20cohomology%20readings/Furman,%20A%20SURVEY%20OF%20MEASURED%20GROUP%20THEORY.pdf).
[Abert--Nikolov, Section 5, Lemma 15](https://ems.press/content/serial-article-files/31852?nt=1)
distinguish it from the known index formula for infimal group cost.
Neither cited result supplies (I). We have proved its equivalence
to (F), not an affirmative answer.

Consequently finite fibers are not a proved general base case for
removing correlated reuse information. In the already solved
cost-one setting, (1) suffices. Outside that setting, replacing
(2) by the unproved equality C(S)-1=q(C(T)-1) would assume exactly
the remaining issue.

Finite-valued observables are also different from finite fibers.
Adjoining all orbit translates of a bit can produce an extension
with uncountably many points in a typical fiber. The finite reuse
localization theorem supplies binary symbolic extensions, not the
uniform finite-fiber hypothesis used here.

The inverse-factor approximation proved in
`fixed-price-conditional-traffic.md`, Section 10, supplies an honest
limit step when a tower of cost-preserving factors is actually
given over a finite-cost base. It does not construct such a tower
for arbitrary symbolic extensions or prove (F) at its finite stages.

## 4. Use in the finite-tail traffic theorem

For a uniform q-point factor with C(Y)<infinity, (1) establishes
the finite-cost base hypothesis needed for Section 9 of the
conditional-traffic artifact. Its exact variational identities
therefore apply even if finiteness of C(X) was not initially known.
The same conclusion follows from (1a) for an ergodic base with
an atomic part in its conditional measures.
This is a real use of the bound in the existing cost-comparison
route. The identities still need simultaneous source optimality
and vanishing conditional defect to prove equality.
