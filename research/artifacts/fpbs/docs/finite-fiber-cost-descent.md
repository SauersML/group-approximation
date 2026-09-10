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

## 5. Selecting fiber labels: a constructive switching bound

Keep the uniform q-point hypothesis. Fix a measurable labeling
ell:Y->{1,...,q} that is a bijection on every fiber. No equivariance
is imposed. Write s_i(x) for the point above x with label i.

First take finitely many full generator demands S. A finite routing
plan D has finitely many partial source maps z->g_j z and bounded
length chosen paths from y to s y on measurable sets E_s. Let N_j(z)
count all occurrences of the edge copy (j,z) in those paths, including
reverse traversals, and put U_j={N_j>0}. Define

    r(D)=sum_s nu(Y\E_s),
    B(D)=r(D)+sum_j nu(U_j),
    W_ell(D)=sum_j integral N_j(z)
                          1_{ell(g_j z)!=ell(z)} dnu(z).

Then

    C(X) <= B(D)+W_ell(D).                                (6)

Here is a direct proof, including the traffic accounting. For each
i, retain the base g_j-edge on

    V_{j,i}={x:s_i(x) in U_j},

and call the resulting graphing Psi_i. Uniform disintegration gives

    (1/q) sum_i sum_j mu(V_{j,i}) = sum_j nu(U_j).           (7)

The left side counts graphing copies separately, which suffices for
an upper bound even if two copies coincide. If a request starting
at y=s_i(x) is covered and no edge along its chosen path changes
ell, every visited point has label i. Each forward edge therefore
projects to a retained Psi_i-edge. For a reverse traversal, its
forward starting point also has label i, so the same assertion
holds. Thus x and s x are connected in Psi_i.

Add a direct s-edge exactly on the measurable set of base requests
not connected in Psi_i. Its indicator is at most the indicator of
an uncovered source request plus the number of label switches on
its chosen path. Average this inequality over i and integrate over
X. For each path word and occurrence, the change of variables from
the request source y to the forward edge start z is a partial p.m.p.
bijection, also for a reverse occurrence. Summing these equalities
identifies the integrated number of switches with W_ell(D). Hence
the average repair cost is at most r(D)+W_ell(D). Every repaired
Psi_i generates the base relation, so some i has completed cost at
most the average B(D)+W_ell(D). This proves (6).

The same proof works for a countable group with a fixed finite-cost
base graphing: route a finite prefix of its partial-domain demands
and include the full remaining base tail in each completed Psi_i.
Include that tail's ordinary cost in r(D), exactly as in Section 9
of the conditional-traffic artifact. Only the routed prefix
contributes to W_ell. No artificial weights on generator demands
are used.

This is a sufficient upper bound, not an exact variational formula.
A label switch need not disconnect the projected request: a different
retained path may already connect it. In particular W_ell is not
the conditional clipping defect J of the traffic theorem.

## 6. A positive switching obstruction with no cost gap

Let Gamma=F_2 x C_2, with free generators a,b and central involution
t. Let X={-1,1}^Gamma with the fair Bernoulli measure and shift
action, and let chi:Gamma->C_2 be projection. On

    Y=X x {0,1},   g.(x,i)=(g.x,i+chi(g)),

use uniform fiber measure and addition modulo two. The projection
Y->X is a uniform two-point free factor. The Bernoulli base is
essentially free; for a nonidentity shift, its coordinate cycles
impose infinitely many independent nontrivial constraints (or an
infinite constant-coordinate constraint), so its fixed set is null.

Every measurable bijective labeling of these fibers has the form

    ell(x,i)=i+c(x),   c:X->{0,1}.

Set S={a,a^(-1),b,b^(-1),t} and

    d_s=mu{c(s.x)!=c(x)+chi(s)}.

For every such c,

    sum_{s in S} d_s >= delta := 2-sqrt(3) > 0.            (8)

To prove this uniformly over all measurable c, put E={c=1},
p=mu(E) and f=1_E-p. The nonconstant Walsh functions

    w_A(x)=product_{h in A} x_h,

indexed by finite nonempty A subset Gamma, form an orthonormal
basis of L2_0(X). The F_2-action on this index set is free: if
hA=A, a power of h fixes an element of A, so h has finite order;
F_2 is torsion-free. Thus the restricted Koopman representation is
a direct sum of copies of the regular representation of F_2.

The averaging operator P over a,a^(-1),b,b^(-1) on the regular
representation has norm at most sqrt(3)/2. For completeness, orient
the four-regular Cayley tree toward a fixed end. Every vertex has
one parent and three children. The operator T summing values at
the children has norm at most sqrt(3): apply Cauchy--Schwarz at
each vertex and use that every vertex has one parent. Adjacency
is T+T*, so its norm is at most 2 sqrt(3). Dividing by four proves
the asserted bound, also on the direct sum.

Consequently

    sum_{s=a^(+/-1),b^(+/-1)} d_s
      = sum_s ||f composed with s - f||_2^2
      >= 8(1-sqrt(3)/2) p(1-p).                           (9)

For t, the desired cocycle bit is one, so

    d_t=1-mu(E symmetric-difference tE) >= |2p-1|.         (10)

With u=|2p-1|, (9)--(10) give

    sum_s d_s >= delta(1-u^2)+u >= delta,

since u(1-delta u)>=0 for 0<=u<=1. This proves (8).

### Why this is an obstruction to a method, not to Fixed Price

Every free action of Gamma has cost 3/2. Indeed choose a measurable
representative set A for its two-point t-orbits, of measure 1/2.
Use the graphing t|A, a|A, b|A. Its internal t-edge connects each
pair. Between the pairs there is exactly one bridge per positive
free generator. The quotient graph on pairs is the Cayley tree of
F_2: normality gives the quotient action, and freeness excludes
any nontrivial free word fixing a pair. Replacing each tree vertex
by its two-point tree and each quotient edge by one bridge gives
a connected tree on the whole Gamma-orbit. This generating treeing
has cost 3/2. Treeings attain relation cost by
[Gaboriau, Theorem 2.24](https://perso.ens-lyon.fr/gaboriau/Travaux-Publi/ME-Cost-L2-Lectures/ME-Cost-L2-lectures.pdf).
In particular C(X)=C(Y)=3/2. This is a known fixed-price family;
no universal finite-index action-cost formula is being assumed.

For any finite routing plan with the full demands S above, a covered
request whose endpoint labels differ has at least one switch along
its path. Uncovered requests cost at most their indicator. The same
traffic change of variables as in Section 5 now gives

    sum_s d_s <= r(D)+W_ell(D),
    r(D)+W_ell(D) >= 2-sqrt(3).                           (11)

Thus, along any sequence with r(D_n)->0, even with labelings ell_n
chosen anew for each plan,

    liminf W_{ell_n}(D_n) >= 2-sqrt(3).                   (12)

Source plans with B(D_n)->3/2 and r(D_n)->0 do exist: use the
generating treeing above and route all requests whose unique paths
have length at most n. Their uncovered measure tends to zero,
B(D_n)<=3/2+r(D_n), and completing them gives B(D_n)>=C(Y).
So a proof strategy demanding simultaneously near-optimal source
budget, asymptotically full coverage, and vanishing W is impossible
even for this cost-preserving two-point factor.

This does not exclude optimal selected graphings Psi_i: (6) may
overcount their actual repair. It does not obstruct vanishing of
the distinct conditional defect J, nor all possible methods using
sections. The precise lesson is that approximate coherence of a
fiber choice is stronger than the required preservation of cost.
