# Fixed Price / Benjamini–Schramm: action-level torsion detours

Date: 2026-09-08.

## Status and provenance

Neither universal conjecture is solved here. The previous exponential-pivotal
necessary condition has not been contradicted: its finite radius is uncontrolled,
and no uniform upper bound is supplied in this continuation.

This note turns to Fixed Price. It derives a finite-pattern, arbitrary-action
version of a torsion-detour construction, obtains upper-cost rigidity among
infinite subgroups of sufficiently large odd free Burnside groups, and gives two
explicit free actions whose costs are equal if and only if the unresolved
Burnside upper cost equals one.

The cycle mechanism is adapted from Donoso-Echenique–Silva [DS], Proposition 2.7.
The extra step here uses finite-pattern approximation in the *given action*, plus
an explicitly paid exceptional set, rather than assuming that independent random
labels are available inside that action. No claim of mathematical priority is made.

The new statements have written proofs with identified inputs. The accompanying
script checks finite algebra and probability only. No Lean/Isabelle/Coq verification
or independent mathematical referee verification has been performed.

## 1. Definitions and imported results

Work with countable groups and essentially free p.m.p. actions on standard
probability spaces. Write right actions as x -> xg; a left action becomes a right
action by inversion. Null sets may be removed after taking their countable group
saturations.

For H <= G, let R_H be the H-orbit subrelation in a specified G-action. A graphing
is a countable family of measure-preserving partial isomorphisms. Its cost is the
sum of their domain measures. C(R) is the infimum over graphings generating R.

Define relative cost by

    rel-C(R; S) = inf{Cost(Psi) : S joined with Psi generates R}.

Thus rel-C(R; S)=0 does not mean that a graphing of additional cost zero attains
that infimum. It implies C(R) <= C(S). It does not imply C(R)=1.

For an infinite group K write

    C^*(K) = sup{Cost(K acting freely and p.m.p. on X)}.

The supremum is used even for infinitely generated groups. We use Bernoulli
attainment only for finitely generated groups, where [AW, Corollary 2] applies.

The following inputs are imported rather than proved by the replay script.

**[AW-pattern]** Every free action of an infinite countable group weakly contains
its Bernoulli actions [AW, Theorem 1]. In particular, for a finite set F <= G,
0<q<1, and eta>0, there is a measurable A in the *original action space* such that

    (1_A(xg))_{g in F},  x sampled from mu,

has distribution within eta in total variation of independent Bernoulli(q)
variables. This is the usual finite-partition formulation of weak containment.

**[Burnside algebra]** For sufficiently large odd n, nontrivial centralizers in
B(m,n), m>=2, are cyclic of order n. Every noncyclic subgroup contains a copy of
B(infinity,n), and hence copies of B(k,n) for every finite k>=2. See [I] and the
precise input statements [DS, Lemma 2.4 and Theorem 2.5]. We keep the exponent
assumption as 'sufficiently large odd' rather than claiming a new numerical bound.

**[Cost induction]** For a complete section Y of R, using normalized measure on Y,

    C(R)-1 = mu(Y) * ( C(R restricted to Y)-1 ).                 (1.1)

See [G, Proposition 2.33]. The direction of the measure factor matters. It was
visually checked against page 15 of the lecture PDF. Also C(R)>=1 when classes
are infinite [G, Corollary 2.35].

**[Bernoulli maximum]** Free Bernoulli actions attain C^*(K) when K is finitely
generated [AW, Corollary 2].

## 2. A finitary zero-relative-cost criterion

### Proposition 2.1

Let G=<H,a> be countably infinite. Suppose there is an integer M>=2 such that for
every k one can choose b_1,...,b_k in H for which

    c_i = a b_i,       2 <= d_i=ord(c_i) <= M,
    P_i = {c_i, c_i^2, ..., c_i^(d_i-1)}

are pairwise disjoint sets.

Then, in every essentially free p.m.p. G-action,

    rel-C(R_G; R_H)=0,                                        (2.1)
    C(R_G) <= C(R_H).                                         (2.2)

More quantitatively, for every 0<q<1, eta>0, and a choice of k such detours,
there is a graphing Psi with R_H joined with Psi equal to R_G and

    Cost(Psi) <= q + (1-q^(M-1))^k + 2 eta.                   (2.3)

### Proof

Use [AW-pattern] on F={e} union P_1 union ... union P_k. Choose A whose finite
label distribution is within eta of the product Bernoulli(q) law. In particular,

    mu(A) <= q+eta.

Define the measurable failure set

    D = {x : for every i there exists 1<=ell<d_i
                 such that x c_i^ell is not in A}.

In the ideal product law the events that all coordinates of P_i are selected are
independent, with probabilities q^(d_i-1). Therefore

    mu(D) <= product_i (1-q^(d_i-1)) + eta
           <= (1-q^(M-1))^k + eta.                           (2.4)

Append to R_H the two restrictions of the transformation T_a:x->xa, one on A
and one on D. Their total cost is at most mu(A)+mu(D).

If x is in D, the added direct edge joins x to xa. Otherwise select a successful
i. Starting at xa, use the following alternating path:

    xa --b_i--> x c_i --a--> x c_i a --b_i--> x c_i^2
       --a--> ... --b_i--> x c_i^(d_i-1)
       --a--> x c_i^(d_i-1) a --b_i--> x c_i^d_i = x.

All b_i steps lie in R_H. Each displayed a-step starts at x c_i^ell in A, for
1<=ell<d_i, so it belongs to T_a restricted to A. Thus x and xa are connected.
Since this holds for almost every x, all a-edges are generated, and the joined
relation is exactly R_<H,a>. All added edges are in that relation, so there is no
overshoot.

If an actual graphing Phi_H of R_H is used instead of treating R_H as already
available, each b_i-step can be replaced by a finite Phi_H-path on a conull
invariant set. No uniform bound on the length of those paths is required.

This proves (2.3). Given delta>0, choose q<delta/3, then choose finite k so that
(1-q^(M-1))^k<delta/3, then eta<delta/6. The relative cost is below delta.
Letting delta tend to zero proves (2.1). Adding these restrictions to an
arbitrarily near-optimal H-graphing proves (2.2). QED.

### Why this is not a hidden Bernoulli-extension argument

No product extension of the given action was substituted for it. The set A lies
on its original probability space. Only finitely many joint label probabilities
are approximated. Every failed connection is paid for by D. There is no passage
to an infinite independent family, no unproved Borel-Cantelli assertion on the
original action, and no connectivity claim about a limiting zero-density graph.

The number k can be enormous; roughly q^(-(M-1)) times a logarithm. Efficiency or
short geometric routes are not part of this result.

## 3. Uniformly finite abelian centralizers give the hypothesis

### Proposition 3.1

Let G be countably infinite and suppose that for some finite M,

    C_G(g) is abelian and |C_G(g)|<=M for every g!=e.           (3.1)

For every infinite subgroup H<=G and every free p.m.p. G-action,

    rel-C(R_G; R_H)=0,
    C(R_G) <= C(R_H).                                        (3.2)

Consequently

    C^*(G) <= C^*(H).                                        (3.3)

### Proof

Distinct nontrivial centralizers have trivial intersection. Indeed, if w!=e
commutes with u and v, then u,v belong to the abelian group C_G(w), hence commute.
Every element of C_G(u) then commutes with v because C_G(u) is abelian. This gives
C_G(u)<=C_G(v), and symmetry gives equality.

Fix a outside H. The infinite coset aH meets infinitely many centralizers, since
each centralizer contains at most M elements. Choose c_i=a b_i in pairwise
different centralizers. Each c_i has order at most M and at least two. Its
nonidentity powers lie in C_G(c_i), so the power sets P_i are pairwise disjoint.
Proposition 2.1 applies.

Enumerate the elements a_j needed together with H to generate G. Each a_j can be
handled relative to the original R_H, with added cost below delta*2^(-j). The
union of all added graphings costs below delta and generates R_G with R_H. This
proves (3.2), even if G and H are not finitely generated. Countable intersections
of the required conull sets preserve the almost-everywhere assertion.

For every G-action, its restricted H-action is free and has cost at most C^*(H).
Taking the supremum over G-actions proves (3.3). QED.

The proof of the disjoint-centralizer fact and the torsion-cycle device are the
mechanism of [DS]. The arbitrary-action, paid-exception formulation here is the
finite-pattern adaptation in Section 2, rather than an assertion that the cited
paper proves fixed price.

## 4. A common upper cost for the large-odd-exponent Burnside family

Fix sufficiently large odd n so the two algebraic inputs in Section 1 hold.

### Theorem 4.1

There is a number c_n such that for every finite m>=2 and every infinite subgroup
H<=B(m,n),

    C^*(H)=C^*(B(m,n))=C^*(B(2,n))=:c_n,                    (4.1)
    1 <= c_n <= 2-2/n.                                     (4.2)

In particular, every free p.m.p. action of every such H has cost at most 2-2/n,
including infinitely generated H.

### Proof

Property (3.1) passes to subgroups. Since H is infinite and all cyclic subgroups
are finite, the subgroup embedding theorem gives a subgroup J<=H isomorphic to
B(m,n). Apply (3.3) twice:

    C^*(B(m,n)) <= C^*(H) <= C^*(J)=C^*(B(m,n)).

This proves equality for H and its ambient Burnside group. Applying it to the
standard embedded B(2,n)<=B(m,n) proves equality across finite ranks.

The two free Burnside generators of B(2,n) have order exactly n. In any free
B(2,n)-action, the orbit relation of each individual cyclic generator can be
spanned by deleting one edge from every n-cycle. A Borel transversal for this
finite equivalence relation exists, and the resulting graphing has cost 1-1/n.
The union of the two graphings generates the B(2,n)-orbit relation. Its cost is
2-2/n. The infinite-class cost lower bound gives the other inequality. QED.

### What (4.1) does and does not compare

It compares *suprema over actions*. It does not assert that every action of a
given Burnside group has cost c_n. In particular it does not permit replacing
C^*(H) by the infimum cost C_*(H).

[DS] proves the already known-to-this-continuation statement C_*(B(m,n))=1 for
large odd n, and explicitly distinguishes it from fixed price one. The uniform
upper bound here leaves a nonzero interval between 1 and 2-2/n.

## 5. Two completely specified free actions, with conditional separation

Set Gamma=B(2,n)=<a,b>. Let

    pi:Gamma -> Z/nZ,       pi(a)=1, pi(b)=0,
    K=ker(pi),             [Gamma:K]=n.

Let alpha be the Bernoulli shift on Omega=[0,1]^Gamma with product Lebesgue
measure. Define another Gamma-action on Omega x Z/nZ with uniform measure on the
second factor by

    beta(g)(omega,j) = (g omega, j+pi(g)).                    (5.1)

Both actions are essentially free: freeness follows from their Bernoulli
coordinate. They are also ergodic. Alpha is Bernoulli ergodic; for beta, its
restriction to K on any one sheet is a Bernoulli K-action, hence ergodic, and
Gamma permutes the n sheets transitively.

### Theorem 5.1

For these two particular actions,

    Cost(alpha)=c_n,
    Cost(beta)=1+(c_n-1)/n.                                 (5.2)

Hence

    Cost(alpha)-Cost(beta)=(1-1/n)(c_n-1),                  (5.3)

and, unconditionally,

    1 <= Cost(beta) <= 1+1/n-2/n^2.                         (5.4)

### Proof

Gamma is finitely generated, so the Bernoulli maximality theorem gives
Cost(alpha)=C^*(Gamma)=c_n.

K has finite index, hence is finitely generated; it is infinite. Theorem 4.1
gives C^*(K)=c_n. Restriction of alpha to K is a Bernoulli K-action: the Gamma
coordinates split into n regular K-orbits, which can be regrouped as a product
base for a K-indexed Bernoulli shift. Thus Cost(alpha restricted to K)=c_n.

The subset Y=Omega x {0} is a complete section of beta's orbit relation and has
measure 1/n. Its restricted orbit relation is exactly that of alpha restricted
to K: a group element returns the second coordinate to zero precisely when it
belongs to K. Equation (1.1) therefore gives

    Cost(beta)-1=(1/n)(c_n-1).

The other formulas follow algebraically. QED.

This is an exact action-cost calculation *in terms of an undetermined number*.
It is not a verified pair of different costs until c_n>1 is established.

### The remaining dichotomy

If c_n=1, then every infinite subgroup covered by Theorem 4.1 has fixed price one.
If c_n>1, the two actions in (5.1) and (5.2) refute the universal Fixed Price
assertion, even with free ergodic actions.

Neither inequality c_n>1 nor equality c_n=1 has been proved here.

## 6. A tempting false inference, and the correct normalization

One might try to combine C^*(K)=C^*(Gamma)=c_n with the formula

    C^*(K)-1 = [Gamma:K]*(C^*(Gamma)-1)                      (UNPROVED HERE)

to obtain c_n=1. That would insert an additional unproved input. The known
finite-index formula for the *infimum over actions* does not authorize the same
formula for a specified restricted action or for upper cost. [AN, Section 5]
carefully distinguishes these questions.

The formula used in Section 5 is instead the established complete-section
induction formula. The sheet Omega x {0} is an actual measurable section of the
*new* action beta. The original Bernoulli Gamma-action alpha was not compressed
by merely restricting the acting group to K. These are different operations.

A useful normalization check: a finite relation with classes of size h has cost
1-1/h. Amplifying each class into d sheets gives cost 1-1/(dh), which equals
1+((1-1/h)-1)/d. This confirms the factor 1/d in the induced-action formula.

The second action beta must not be identified with a Bernoulli action merely
because it has a Bernoulli coordinate. It is not mixing: its sheet Y has measure
1/n, and for every g in the infinite subgroup K one has gY=Y, so
mu(Y intersection gY)=1/n rather than 1/n^2. Bernoulli actions are mixing, as
can be checked first on cylinder events by disjointness of distant finite
coordinate sets and then by approximation. This distinction alone does not
prove a difference of costs.

## 7. Why this does not close Benjamini–Schramm

The prior necessary exponential-pivotal condition remains conditional. This
continuation provides no upper bound uniform in radius on those conditional
pivotal counts.

There is still the established implication [L]

    no nonuniqueness interval on a Cayley graph -> fixed price one.

If c_n>1, that implication gives nonuniqueness for Cayley graphs of the relevant
finitely generated Burnside subgroups, while the actions above would refute
Fixed Price. If c_n=1, it supplies no percolation conclusion for these groups.
Neither side of this dichotomy settles the universal Benjamini–Schramm claim.

## 8. Finite verification and Cairn semantics

`scripts/replay_torsion.py` uses exact permutations in A5 and exact rational
probabilities. It checks centralizer intersections, the alternating detour path,
all selector configurations for a finite three-detour fixture, the independent
failure product, and induced-cost normalization. A5 is just a finite algebra
test fixture. Its finite cosets cannot verify the infinite hypothesis of
Proposition 2.1.

The script does not prove weak containment, Burnside algebra, infinite measured
connectivity, cost infima, or c_n=1/c_n>1. Those mathematical issues are addressed
only by the written arguments and published inputs stated above, with the last
dichotomy explicitly unresolved.

The additive Cairn package retains prior work as provenance. A dependency check
validates node syntax, references, and the recorded implication graph, not the
truth of a proof. Both universal goals remain OPEN. There is no route from the
new conditional counterexample formula to a solved universal goal without a
proved strict lower bound c_n>1.

## References

[AW] Miklos Abert and Benjamin Weiss, *Bernoulli actions are weakly contained in
any free action*, arXiv:1103.1063v2 (2011), Theorem 1 and Corollary 2.
https://arxiv.org/html/1103.1063v2

[DS] Miguel Donoso-Echenique and Eduardo Silva, *Free Burnside groups of large odd
exponent have cost 1*, arXiv:2608.20472v1 (20 August 2026), especially the explicit
infimum/fixed-price distinction after Theorem 1.2, Lemma 2.3, Lemma 2.4,
Theorem 2.5, and the torsion-detour construction in Proposition 2.7.
https://arxiv.org/html/2608.20472v1

[I] S. V. Ivanov, *On subgroups of free Burnside groups of large odd exponent*,
arXiv:math/0210191 (2002), Illinois Journal of Mathematics 47 (2003), 299-304.
https://arxiv.org/abs/math/0210191

[G] Damien Gaboriau, *Around the orbit equivalence theory, measure equivalence,
cost and L2 Betti numbers* (lecture PDF accessed 8 September 2026), Proposition
2.33 and Corollary 2.35, printed page 15; relative cost in Definition 2.38.
https://perso.ens-lyon.fr/gaboriau/Travaux-Publi/ME-Cost-L2-Lectures/ME-Cost-L2-lectures.pdf

[AN] Miklos Abert and Nikolay Nikolov, *Rank gradient, cost of groups and the rank
versus Heegaard genus problem*, arXiv:math/0701361v3 (2008), Section 5, especially
the distinction preceding Lemma 15. The old paper's unrelated historical open
questions are not being asserted as current.
https://arxiv.org/html/math/0701361v3

[L] Russell Lyons, *Fixed price of groups and percolation*, arXiv:1109.5418v1
(2011). Qualitative implication only; not a universal resolution.
https://arxiv.org/html/1109.5418v1
