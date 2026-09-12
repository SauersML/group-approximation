# Nonnegative local pattern energy and finite-configuration surjectivity

Date: 2026-09-08. This proves the implication in
`pattern-energy-token-corners-prove-surjectivity`, conditional only on
the established collision-program theorem
`relative-equality-piecewise-injections-are-surjective`. It makes no
claim to settle Gottschalk's conjecture or establish external novelty.

## Conventions and hypotheses

The left G-action on configurations is (h.x)(g)=x(h^(-1)g). Local
neighborhoods are right translates: tau(x)(g) depends on x|_(gM),
where M is finite and contains 1. The vacuum is 0^G and tau fixes it.
All injectivity hypotheses below concern finite-support configurations.

Let P be finite, 1 in P, and e:A^P->[0,infinity), e(0^P)=0. Put

    e_g(x)=e((x(gp))_(p in P)),
    B(x)={g:e_g(x)>0},
    E(x)=sum_g e_g(x).

Assume that the simultaneous zero locus of the e_g is exactly {0^G}
and that E(tau(x))<=E(x) for every finite-support x. For such x,
B(x) is finite: a nonzero energy pattern meets supp(x), so
B(x) is contained in supp(x)P^(-1).

If A={0}, the conclusion is immediate. Otherwise some pattern has
positive energy, and the following positive weight list is nonempty.

## 1. Compactness supplies local detection and a support bound

For every configuration with x(1)!=0 there is some g with e_g(x)>0.
The cylinder {x:x(1)!=0} is compact, and the sets {x:e_g(x)>0}
are open. There is a finite F in G such that

    x(1)!=0 => e_f(x)>0 for some f in F.               (1)

Translating (1) gives, for every x and occupied h, a center hf in B(x).
Choose a finite symmetric D containing 1 and F. Then

    supp(x) subset B(x)D,
    |supp(x)| <= |D| |B(x)|                            (2)

for finite x. Conversely, such a detection set implies that a
configuration with every e_g zero is the vacuum. Thus (1) is an exact
finite characterization of the simultaneous zero-locus hypothesis.
It does not assert an algorithm for recognizing that hypothesis over
an arbitrary group.

This step is where merely having no nonzero *finite* zero-energy
configuration would be insufficient. For the binary nearest-neighbor
disagreement energy on Z, every nonempty finite interval has energy
two while its support can be arbitrarily large; the all-one infinite
configuration is also in the zero locus. That energy has no bound (2).

## 2. Preserve real equalities with integer pattern packets

List all patterns p in A^P with e(p)>0, and write w_p=e(p). Let L be
the rational span of the integer vectors d satisfying w dot d=0.
Its real annihilator is a rationally defined linear subspace containing
the strictly positive vector w. Choose a positive rational vector in
this annihilator, and scale it to a positive integer vector v. Then

    w dot nu=w dot eta => v dot nu=v dot eta             (3)

for nonnegative integer pattern-count vectors nu,eta. This does not
require the integer weights to preserve inequalities.

The candidate levels Q={w dot nu:nu in N^k} are locally finite in
[0,infinity), because each coordinate of nu is bounded on bounded
energy intervals. Define N(q)=v dot nu when w dot nu=q; (3) makes
this well-defined. For an actual positive level, N(q)>=1.

Put R=D union P, a finite set containing 1. For every center g in
B(x), write r_g=(x(gr))_(r in R) and p_g=r_g|_P. Give x the tokens

    (g,r_g,j),          1<=j<=v_(p_g).                  (4)

Thus every energy-q configuration has exactly N(q) tokens. Tokens
at the same site carry one common R-pattern and a complete packet of
the indicated indices. Crucially, the unordered token set determines
x: read its R-patterns on B(x)R and put zero elsewhere. Equation (2)
guarantees that no occupied site is lost. Translation of x translates
its token centers while leaving all token labels unchanged.

## 3. Ordered token sectors are finite relative-equality domains

Fix q>0 with N=N(q). Let X_q consist of every ordering of the N
tokens of every finite-support configuration of energy q. Token
labels belong to a fixed finite alphabet, so X_q is a subset of
C x G^N for a finite control set C. We check that it is definable
using finitely many tests g_i^(-1)g_j=s.

Given a candidate token list, first test packet completeness, absence
of repeated tokens, and consistency of the R-patterns on overlapping
sets g_i R. An overlap g_i a=g_j b is exactly the allowed test
g_i^(-1)g_j=a b^(-1), with a,b in R. The consistent list defines a
finite configuration x by its patches, with zero outside their union.

Recompute its charged centers and their labels. Since e(0^P)=0, any
charged center lies in supp(x)P^(-1), hence in the finite candidate
list of positions g_i a p^(-1), a in R, p in P. Testing the P-pattern
and the R-pattern at these positions uses only comparisons between
finitely many position expressions g_i s. Compare the recomputed
token packets with the original list and reject unless they agree
exactly. Finally test energy q, which is a finite control-state test
on the packet labels and their multiplicities.

Every comparison of position expressions reduces to a relative
equality. There are only finitely many tests, since N,R,P and the
label sets are fixed. A genuine token list passes. A passing list
equals the complete token set of its reconstructed configuration,
which has energy q. This proves the precise collision-domain claim;
no unconstrained full-shift extension of a pattern presentation is
being assumed.

## 4. Lower levels force conservation at the next level

Induct over the locally finite ordered set Q. Energy zero contains
only the vacuum, which is fixed and attained. Suppose every actual
level below q is preserved and attained. If E(x)=q and E(tau(x))<q,
the inductive hypothesis supplies z with E(z)=E(tau(x)) and
tau(z)=tau(x). Finite injectivity would give z=x, a contradiction.
The assumed nonincrease therefore implies E(tau(x))=q.

Conservation has now been proved for all finite configurations with
energy at most q. To complete this induction step, it remains to
show that tau attains every configuration of energy q.

## 5. One large interaction neighborhood separates whole token sets

Set U=R union RM and J=U^(-1)U. The set J is finite, symmetric, and
contains 1. Partition S=supp(x) into the connected components for
edges s^(-1)t in J. Write x_C for the restriction to one component C,
with vacuum elsewhere. No translated U-neighborhood meets two
components: two such sites would have relative difference in J.

Several consequences follow directly from this single observation.

* A translated M-neighborhood sees at most one component, so
  tau(x) is the disjoint superposition of the tau(x_C).
* A translated R-neighborhood sees at most one component. Since
  P subset R, the input charged patterns and their complete decorated
  token sets are the disjoint union of those of the x_C.
* An output R-pattern depends only on an input RM-neighborhood.
  Thus output charged patterns and their complete decorated token
  sets are the disjoint union of those of the tau(x_C).

For the last two assertions, a positive P-pattern has an occupied
site, hence selects a component; every occupied site in its larger
neighborhood must belong to that same component. Patterns whose
whole neighborhood is vacuum contribute no tokens.

In particular, E(x)=sum_C E(x_C), with nonnegative summands. Every
x_C has energy at most q. The conservation already obtained in the
induction step gives E(tau(x_C))=E(x_C), and (3) makes their token
counts equal. Let T_C and T'_C denote these two finite token sets.

Each component has at most |D| N sites by (2), because each positive
energy center contributes at least one token. Rooting a component at
one occupied site places its support in J^(|D| N-1). Hence only
finitely many translated component types occur at this level. This
is true over arbitrary G: J is finite and the exponent is fixed.

## 6. Match equal-size free stabilizer sets without a truncation law

For a nonempty component configuration x_C, its translation
stabilizer H is finite. Indeed it acts freely on its finite nonempty
support by left multiplication. The group H preserves both T_C and
T'_C: the first assertion is translation covariance of the encoding,
and the second also uses equivariance of tau. Both actions are free,
since fixing a token forces its group coordinate to be fixed.

The two token sets have equal finite cardinality, so they have the
same number of H-orbits. Pair the H-orbits arbitrarily; on each pair
choose representatives t,t' and send h.t to h.t'. This defines an
H-equivariant token bijection b_C:T_C->T'_C. It needs neither an
ordering of G nor a Hall inequality for energy under truncation.

Choose one such bijection for each of the finitely many translation
types of x_C. Translate it to every copy. Its H-equivariance ensures
that the translated choice does not depend on which translation from
the representative was selected. The selected map is a function of
the configuration, independent of any ordering of its tokens.

For a matched pair with centers g,g', its displacement g^(-1)g' is
constant under common left translation. There are finitely many
component representatives and finitely many tokens in each, so the
entire matching uses finitely many displacements at this q. No bound
independent of q is asserted or needed.

## 7. The lifted map satisfies the exact collision-program hypotheses

For an ordered list in X_q, reconstruct x, and send each token to
its matched token under the union of the b_C. This gives F_q:X_q->X_q.
In coordinate i it has the form g_i->g_i h_i; the output token label
is another finite control state.

To verify its finite piecewise definition, reconstruct supp(x) from
the patches as in Section 3. It is contained in finitely many named
positions g_i r. Test their pairwise J-adjacencies and their symbols.
Since there are at most N|R| such named positions, finding components
is a finite decision tree of relative-equality tests, with no
unbounded connectivity procedure. Their actual supports have the
stronger bound |D|N. For each component, its symbol pattern and
relative positions identify one of the finitely many types above.
Possible representatives can be recognized by finitely many tests
against their fixed relative offsets. Stabilizer equivariance makes
all choices of a recognizing root yield the same token matching.

Thus each branch has fixed output labels and fixed h_i, exactly as
required by `relative-equality-piecewise-injections-are-surjective`.

If F_q sends two input lists to the same output list, the latter
decodes to one configuration tau(x). Finite injectivity determines
x uniquely. The chosen matching for x is a bijection of token sets,
so the output ordering determines the input ordering as well. Hence
F_q is injective. The required collision theorem implies it is onto.
Every ordering of every output energy-q configuration therefore has
a preimage, and tau is onto this configuration sector.

This completes the induction. Every finite configuration is attained
and preserves its energy. Finite configurations are dense in A^G;
the image of the continuous map tau is compact and hence closed in
the Hausdorff full shift. The image is therefore all of A^G.

## 8. The hypotheses strictly exceed positive single-site charges

Over Z let A=F_2^2, with vacuum (0,0), and put

    rho(a,b)_i=(a_i+b_(i+1),b_i),
    S(a,b)_i=(b_i,a_i),
    tau=rho S rho.

All additions here are modulo two. Both rho and S are involutions,
so tau is an involution. Define e_i(x)=1_(rho(x)_i!=(0,0)). This is
a nonnegative local pattern density, and all e_i vanish if and only
if rho(x)=0, equivalently x=0. Further,

    rho tau = S rho,

so E(tau(x))=|supp(S rho(x))|=|supp(rho(x))|=E(x).

Direct substitution yields

    tau(a,b)_i=(b_i+a_(i+1)+b_(i+2), a_i+b_(i+1)).

Let x have a single (1,0) at 0. Its image has (1,0) at -1, (0,1)
at 0, and vacuum elsewhere. Therefore a single-site charge w with
w(0,0)=0 and w(1,0),w(0,1),w(1,1)>0 strictly increases on this x:

    W(tau(x))-W(x)=w(0,1)>0.

Thus no positive single-site charge nonincrease theorem applies to
this tau, while the pattern-energy hypotheses do. This is an exact
algebraic example, not a computational search result.

## 9. Literature/status audit and the remaining endpoint

Repository search on 2026-09-08 found the single-site charge results
and the existing collision theorem, but no matching local-pattern
energy extension. The route above imports only the collision theorem;
its finite-domain encoding and stabilizer matching are proved here.

The integration audit was repeated against authoritative remote main
`f80ca6a9456fc025c7c12370fcc3a09175f08fd6`, which was 268 commits
ahead of the initial local HEAD `d63764e04`. Read-only tree searches,
content searches, and diffs found no local-pattern-energy counterpart.
The collision-algebra claim, its partition-polynomial proof, the
relative-equality program claim and proof, and all three positive
single-site charge claims were unchanged between those revisions.
The remote collision validation artifact records them as established,
while explicitly limiting its machine check to graph compilation and
artifact/reference lint, with handwritten mathematical review.

Remote main additionally contains quantitative observable-defect ranks,
generic Cantor decoder fibers, and quantum-compression obstruction
bounds, in `split-ca-defects-force-linear-observable-rank`,
`split-decoders-have-generic-cantor-fibers`, and
`split-ca-quantization-has-sharp-defect`. Those results assume a
cellular section and isolate other open surjunctivity criteria; none
states energy nonincrease or supplies the token-sector implication
proved here. They neither duplicate this theorem nor invalidate its
collision foundation. Its relation to the new universal positive root
`gottschalk-surjunctivity-conjecture` is a proved restricted class,
not a route establishing the unrestricted root.

Local interaction energies are established terminology and are not
claimed as a new concept. Siamak Taati's 2009 dissertation,
[Conservation Laws in Cellular Automata](https://siamak.isoperimetric.info/articles/thesis.pdf),
Chapter 2 develops local pattern potentials. Theorem 4.20, attributed
there to Formenti and Grange, starts with a *surjective* CA over Z and
a conserved real local potential difference with a unique ground
configuration, and concludes density of temporally periodic points.
It does not state the arbitrary-group implication proved above.
Its ground-configuration definition uses local energy improvements;
we instead require explicitly a nonnegative density with singleton
simultaneous zero locus. These hypotheses must not be conflated.

Jarkko Kari and Siamak Taati,
[Statistical Mechanics of Surjective Cellular Automata](https://doi.org/10.1007/s10955-015-1281-2),
work on lattice shifts and relate conserved Hamiltonians to invariant
Gibbs measures under surjectivity assumptions. Their result supplies
neither the arbitrary-group collision finiteness used here nor the
deduction of surjectivity from energy nonincrease. Marcus Pivato's
[Conservation Laws in Cellular Automata](https://arxiv.org/abs/math/0111014)
is a further primary reference for additive conservation laws; the
earlier repository literature audit records its precise scope.

The current [Gottschalk problem record](https://github.com/google-deepmind/formal-conjectures/issues/2152)
and Bowen--Chapman's [2025 primary paper](https://arxiv.org/abs/2511.06586)
were checked on 2026-09-08. The latter describes general surjunctivity
as open and proves an IRS result, not an arbitrary-group resolution.
This focused search is not an exhaustive novelty certification. No
supplementary algorithm or code is invoked as the source of the
theorem; the argument and example above are exact and symbolic.

For `leavitt-unit-group-nonsurjunctive`, this gives a stronger design
restriction: a finite-injective strict encoder fixing the vacuum
cannot conserve or dissipate any nonnegative local pattern energy
whose zero locus is exactly the vacuum. The existence of such an
energy is not automatic for a general CA. Finding a counterexample
outside this class, or deriving a more general positive theorem,
remains the unresolved full-shift endpoint.
