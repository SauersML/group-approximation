# Bounded exponent, relative cost, and fixed price one

Research continuation — September 8, 2026

## Status and scope

This note supplies written proofs of a subgroup-relative-cost theorem for **all countable bounded-exponent groups**, a quantitative fixed-price criterion from large finite subgroups, and concrete applications. In particular, together with Held's established algebraic theorem, the argument proves fixed price one for every countably infinite group of exponent a power of two. A published locally finite subgroup theorem also gives the conclusion for the large even free Burnside groups specified below.

No novelty or priority claim is made. These arguments have not been independently refereed or formalized. The accompanying replay checks finite algebra and finite counting only. Neither the universal Fixed Price problem nor the universal Benjamini–Schramm conjecture is asserted solved. The previous odd-exponent Burnside upper-cost constant remains undetermined.

The principal change from the previous note is that **a collision among torsion detours is usable information**: it identifies a centralizer through which an element can be added cheaply. First returns to the current subgroup remove shared powers that have already been absorbed. No condition that centralizers be finite or abelian remains.

## 1. Conventions and elementary cost facts

Let G be a countably infinite group acting essentially freely and probability-preservingly on a standard probability space (X,mu). Discard an invariant null set so the action is free, and write it on the right: T_g(x)=xg. For K<=G, write R_K for its orbit equivalence relation.

A graphing is a countable family of partial measure-preserving bijections, with cost the sum of the measures of their domains. Relation cost is the infimum over generating graphings. Define

    relC(R;S) = inf { cost(Psi) : S joined with R_Psi equals R }.

Every partial bijection in this note is a restriction of a group transformation (or a finite measurable union of such restrictions). Equality of relations is understood on invariant conull sets. The assertion relC=0 concerns an infimum: an attaining graphing of zero cost is not being asserted.

We use the standard lower bound C(R)>=1 for free actions of infinite groups [G]. For a free finite-group action, |F|=h, there is a generating treeing of cost 1-1/h: choose a measurable transversal A of measure 1/h, and for each g in F\{e} use T_g restricted to A. Standard Borel finite equivalence relations have such transversals. This also directly proves the needed upper bound without an imported minimization theorem.

For an infinite countable locally finite group L, every free action has cost one. Here is the upper-bound construction. Write L as a strictly increasing union of finite groups L_j of orders h_j tending to infinity. Start with trees on L_1-orbits. Within each L_{j+1}-orbit, connect its L_j-orbit trees using a tree on the quotient set of suborbits. This adds cost

    1/h_j - 1/h_{j+1}.

Measurable finite transversals make these choices Borel. The resulting increasing union of graphings generates R_L and has total cost

    (1-1/h_1) + sum_j (1/h_j-1/h_{j+1}) = 1.

The lower bound gives equality. In particular, every infinite torsion abelian subgroup is an available fixed-price-one subgroup, since a finitely generated torsion abelian group is finite.

Set C*(G)=sup_alpha C(alpha), over free p.m.p. G-actions. None of the arguments below needs a theorem identifying which action attains this supremum.

## 2. A finite coloring lemma on the original action

**Lemma 2.1 (finite separation and derandomization).** Let F be a finite set of distinct elements of G, and let eta>0. There is a finite measurable partition P of X such that, outside a set of measure less than eta, all points xg, g in F, lie in different atoms of P.

**Proof.** Take increasing finite measurable partitions that separate points of the standard Borel space. For g!=h, freeness gives xg!=xh almost surely. The probability that these two points remain in the same atom decreases to zero. A finite union bound over pairs in F proves the claim. QED.

Independently select the finitely many atoms of P with probability q, and let A be their union. This randomness is only a finite auxiliary probability space; a deterministic assignment will be selected by averaging. It is not a change of the original action.

Suppose P_1,...,P_k are disjoint finite subsets of F, with t_i=|P_i|. Define

    D(A) = {x : for every i, some g in P_i satisfies xg not in A}.

For every good x from Lemma 2.1, the tested atom labels are independent, so the conditional probability of D(A) is product_i(1-q^t_i). Therefore

    E_colors mu(A) = q,
    E_colors mu(D(A)) <= product_i(1-q^t_i) + eta.

Some deterministic A consequently satisfies

    mu(A)+mu(D(A)) <= q + product_i(1-q^t_i) + eta.       (2.1)

Only this sum is needed. No independent bounds on the two terms for the selected A are asserted. No infinite independent labeling, weak-containment theorem, or limiting connected graph is required.

## 3. Two ways to add an element cheaply

### 3.1. First-return torsion detours

**Lemma 3.1.** Let K<=G, a outside K. Suppose, for arbitrarily large k, there are b_i in K and integers 2<=d_i<=N such that

    c_i=a b_i,   c_i^d_i in K,
    P_i={c_i,c_i^2,...,c_i^(d_i-1)}

are disjoint sets of elements outside K. Then, in the given free action,

    relC(R_<K,a>;R_K)=0.

For each such finite family, each 0<q<1, and each eta>0, an extension graphing can be chosen with cost at most

    q + (1-q^(N-1))^k + eta.                              (3.1)

**Proof.** Apply (2.1) to the disjoint P_i. Retain T_a on A and on D(A). If x is a failure, the latter is its direct a-edge. Otherwise some i is successful. The following path joins xa back to the K-orbit of x:

    xa --b_i--> x c_i --a--> x c_i a --b_i--> x c_i^2
       --a--> ... --b_i--> x c_i^d_i --c_i^(-d_i)--> x.

Each b_i-step and the final step lie in R_K. Every a-step starts at x c_i^j in A, for 1<=j<d_i. Thus every a-edge is generated. The additional cost is bounded by (2.1), and t_i=d_i-1<=N-1 gives (3.1). Choose q small, then finite k large, then eta small. QED.

The endpoint condition is c_i^d_i in K, not necessarily c_i^d_i=e. In a nonnormal subgroup K this is a statement about powers meeting K; no quotient group structure is used. If R_K is represented by an actual graphing, its steps can be expanded into finite graphing paths on a common conull set. Their lengths need not be uniformly bounded.

### 3.2. Centralizer connections

**Lemma 3.2.** If L=K intersect C_G(w) is infinite, then

    relC(R_<K,w>;R_K)=0.                                  (3.2)

If L is finite, of order ell, then the same relative cost is at most 1/ell.

**Proof, infinite case.** Choose k distinct l_i in L. Apply Lemma 2.1 and (2.1) to singleton sets {l_i}. Keep the w-edge on A and repair every root for which none of xl_i lies in A. The cost is at most q+(1-q)^k+eta. A successful root is connected by

    x --l_i--> x l_i --w--> x l_i w=xw l_i --l_i^(-1)--> xw.

Let the bound tend to zero.

**Finite case.** Choose a measurable transversal A for the free L-action. It has measure 1/ell, and every x has xl in A for some l in L. The same path, using T_w only on A, generates all w-edges. QED.

This is the familiar sparse-centralizer mechanism, but its elementary proof has been included to specify the action and the exact cost paid.

## 4. The bounded-exponent subgroup theorem

**Theorem 4.1.** Suppose there is a fixed integer N>=2 with g^N=e for every g in G. For every infinite subgroup H<=G and every essentially free p.m.p. G-action alpha,

    relC(R_G;R_H)=0,                                      (4.1)
    C(alpha)<=C(alpha restricted to H),                   (4.2)
    C*(G)<=C*(H).                                        (4.3)

No centralizer commutativity, centralizer cardinality bound, finite generation, or subgroup normality is assumed.

**Proof.** Work throughout in the specified action.

First, relative-cost-zero extensions are closed under countable joins. If K_j>=H and relC(R_Kj;R_H)=0, choose generating additions of costs less than epsilon 2^(-j-1). Their union, together with R_H, generates the relation of the subgroup generated by all K_j at total additional cost less than epsilon. Relative-cost-zero extensions are also transitive by splitting an error budget into two parts.

There is therefore a largest subgroup K containing H with relC(R_K;R_H)=0. To justify “largest” without an uncountable cost sum, for each group element that belongs to some such subgroup choose one witness subgroup. There are only countably many elements. The join of these witness subgroups is again such a subgroup and contains every one of them.

By Lemma 3.2 and maximality,

    w outside K  implies  |K intersect C_G(w)|<infinity.   (4.4)

Suppose a outside K. The coset aK is infinite. For c in aK define its first return

    d(c)=min{j>=1 : c^j in K}.

The exponent law gives 2<=d(c)<=N. Set

    P(c)={c,c^2,...,c^(d(c)-1)} subset G\K.

These powers are distinct: an earlier repetition would give a smaller positive power equal to the identity and hence in K.

For any fixed w outside K, only finitely many c in aK satisfy w in P(c). Such c commute with w, and

    aK intersect C_G(w)

is either empty or a translate of K intersect C_G(w). Indeed, if c_0 belongs to the intersection, it is exactly c_0(K intersect C_G(w)). It is finite by (4.4).

It follows that arbitrarily many of the finite sets P(c) can be chosen disjointly. At each greedy step, the union of the previously chosen sets is finite. Every element in that union occurs in only finitely many remaining P(c), so only finitely many c are excluded. The infinite coset still supplies another choice.

Lemma 3.1 now gives relC(R_<K,a>;R_K)=0. Transitivity contradicts the maximality of K. Hence K=G, proving (4.1). Append arbitrarily cheap generating additions to a nearly optimal H-graphing to obtain (4.2). Taking the supremum over G-actions gives (4.3), since each restriction is a free H-action. QED.

### What replaced the old hypothesis

The preceding note required nontrivial centralizers to be uniformly finite and abelian. Here one first absorbs every element whose centralizer meets the current subgroup infinitely. Remaining external powers then have finite fibers in the relevant coset. Cutting a torsion cycle at its **first** return ensures that every power tested is still external. The disjointness argument is thus recovered after enlargement, instead of assumed at the start.

### Immediate transfer principle

If a bounded-exponent group contains any infinite subgroup of fixed price one, it has fixed price one. In particular this holds if it contains an infinite locally finite subgroup. This conclusion applies to every original action, not just a selected action or extension.

## 5. A uniform upper bound below two

**Corollary 5.1.** Every countably infinite bounded-exponent group has C*(G)<2. More explicitly, if G is not locally finite, there is a finite subgroup F of order f and an element a of order m<=N such that <F,a> is infinite, and

    C*(G)<=2-1/f-1/m<2-1/N.                               (5.1)

If G is locally finite, C*(G)=1, so it also lies strictly below 2-1/N.

**Proof.** For G not locally finite, choose a finite ordered generating set for an infinite finitely generated subgroup, and stop at the first infinite prefix. The preceding prefix generates a finite F, and the last element is a. The union of a finite-F treeing and a finite-cyclic-<a> treeing generates R_<F,a> at cost at most (1-1/f)+(1-1/m). Apply Theorem 4.1 from this infinite subgroup to G. The same algebraic F,a work for every action. QED.

This does not establish that C*(G)=1 when finite subgroup orders stay bounded.

## 6. A finite packing-versus-centralizer dichotomy

Let K<=G be finite of order t and a outside K. For each c in aK use d(c) and P(c) as in Section 4. Fix an integer k>=2.

**Lemma 6.1.** At least one of the following holds:

1. There are k pairwise disjoint sets P(c), giving the extension bound (3.1).
2. There is w outside K with

       |K intersect C_G(w)| >= t / ((k-1)(N-1)),           (6.1)

   and consequently

       relC(R_<K,w>;R_K) <= (k-1)(N-1)/t.                (6.2)

**Proof.** Take a maximal disjoint family. If its cardinality is at least k, use k of its members. Otherwise its union W has at most (k-1)(N-1) elements, all outside K, and intersects every P(c). Thus

    t <= sum_(w in W) #{c in aK : w in P(c)}
      <= sum_(w in W) |aK intersect C_G(w)|
      <= sum_(w in W) |K intersect C_G(w)|.

The last inequality uses the coset identity established in Section 4. Some w satisfies (6.1); the finite part of Lemma 3.2 proves (6.2). QED.

The k=1 alternative is automatically of the first kind. The displayed denominator is used only in the second kind, where k>=2.

## 7. Large finite subgroups force fixed price one

**Theorem 7.1 (quantitative version).** Suppose G is countably infinite and g^N=e for every g. If G has a finite subgroup of order h>=3, then

    C*(G) <= 1 + ((N-1) log(h)/h)^(1/N).                  (7.1)

In particular,

    finite subgroup orders unbounded  =>  fixed price one. (7.2)

The finite subgroups in (7.2) are not assumed nested, normal, or almost normal, and no intersection estimates for their conjugates are assumed.

**Proof.** Put

    q_t=((N-1) log(t)/t)^(1/N),  t>=3.

This decreases with t because log(t)/t decreases for t>=3. If q_h>=1, (7.1) follows from Corollary 5.1. Suppose q_h<1. Fix an arbitrary free p.m.p. action.

If G is locally finite, its cost is one. Otherwise start with the given finite subgroup F, and append finitely many generators of an infinite finitely generated subgroup until the first infinite step. This yields a finite K_0 containing F and a fixed a outside K_0 with <K_0,a> infinite.

At a stage with K finite, K>=K_0 and t=|K|, let q=q_t and

    k=ceil(t q/(N-1)).

Then

    k q^(N-1) >= log(t),
    (1-q^(N-1))^k <= 1/t,
    (k-1)(N-1)/t < q.                                    (7.3)

Apply Lemma 6.1 to K,a.

In its first case, the infinite subgroup J=<K,a> is generated from R_K with additional cost at most q+1/t+eta. Start with an optimal finite-K graphing, of cost 1-1/t. Thus C(alpha restricted to J)<=1+q after eta tends to zero. Theorem 4.1 extends this to all of G at arbitrarily small additional cost. Hence C(alpha)<=1+q<=1+q_h.

In the second case, obtain w outside K whose connections cost strictly less than q by (7.3). If J=<K,w> is infinite, start with the finite-K graphing to get C(alpha restricted to J)<1-1/t+q, and use Theorem 4.1 again.

If <K,w> is finite instead, replace K by this strictly larger finite subgroup. Crucially, at the next stage **discard the previous finite presentation and use a fresh optimal finite-group graphing**. The costs of earlier finite enlargements are not accumulated. The same a still works: <K,a> contains the original infinite <K_0,a>, so a remains outside the finite K. Also q_|K| does not increase.

Either a successful infinite subgroup is obtained at a finite stage, proving the bound above, or the process yields an infinite strictly increasing chain of finite subgroups. Their union L is an infinite locally finite subgroup. Section 1 gives cost one for alpha restricted to L, and Theorem 4.1 gives cost one for alpha itself.

The argument applies to every alpha with the same bound (7.1). Finally, let finite subgroup orders h tend to infinity, and use the infinite-action lower bound one to obtain (7.2). QED.

This proof never relies on connectivity surviving a weak limit of sparse graphs. In the infinite branch a genuine locally finite subgroup is constructed, and its separately constructed increasing graphing generates its full orbit relation.

### Quantitative obstruction for the remaining case

If delta=C*(G)-1>0, then every finite subgroup of order h>=3 satisfies

    delta^N h <= (N-1) log(h).                            (7.4)

Since h/log(h) tends to infinity, finite subgroup orders must be uniformly bounded. Thus any bounded-exponent group with upper cost greater than one must lie in the bounded-finite-subgroup case. The theorem does not assert the converse.

## 8. Concrete fixed-price-one consequences

### 8.1. Every infinite bounded-exponent 2-group

**Corollary 8.1.** For each integer r>=1, every countably infinite group satisfying g^(2^r)=e for every g has fixed price one.

**Proof.** Held [H, theorem on page 97] proves that every infinite 2-group contains an infinite abelian subgroup. That subgroup is torsion, hence locally finite. Apply the transfer principle following Theorem 4.1 and the locally finite calculation in Section 1. QED.

The original two-page Held paper was visually checked. It proves the infinite-abelian-subgroup assertion, not merely the weaker unbounded-finite-subgroup assertion. Ivanov [I, page 68] also records the latter consequence.

The adjective **bounded-exponent** remains essential to this argument. Held's theorem applies to all 2-groups, but Theorem 4.1 does not apply to a 2-group whose element orders are unbounded. No conclusion about costs of those groups follows here.

### 8.2. An explicit family of large even free Burnside groups

**Corollary 8.2.** Let m>=2 and let n be even with

    n>=2^48,  and  2^9 divides n.

Then B(m,n) has fixed price one.

**Proof.** Ivanov's ICM survey [I, Theorem 1(a)] supplies infinitude in this range. Theorem 3(c) and the subsequent corollary, reporting joint work with Olshanskii [IO], supply infinite locally finite subgroups. For example, the countable direct sum of copies of C_2 embeds: it is a countable subgroup of the product of the involution subgroups used to define E. Apply Theorem 4.1. QED.

In particular, every free p.m.p. action of B(2,2^48) has cost one. This also follows directly from Corollary 8.1 once infinitude is known. The quoted exponent range is conservative and is not asserted optimal. No claim about novelty of this consequence is made.

### 8.3. What is not covered

The argument does not determine the common upper cost c_n from the previous note for sufficiently large **odd** free Burnside groups. Their finite subgroups are cyclic of bounded order in the algebraic range under discussion [I, Theorem 1(e); DS]. The large-finite-subgroup hypothesis therefore cannot be invoked there.

Theorem 4.1 does strengthen subgroup cost comparison for those groups and for arbitrary bounded-exponent groups, but it does not manufacture a cost-one infinite subgroup inside a group all of whose usable infinite subgroups have unknown cost.

Theorem 7.1 also does not settle arbitrary groups that fail bounded exponent. Free groups, for instance, contain infinite cyclic cost-one subgroups, but no counterpart of Theorem 4.1 is claimed for them.

No step here proves p_c<p_u for all nonamenable Cayley graphs. The cost-one percolation case remains beyond the known positive-cost implication. These fixed-price-one conclusions must not be relabeled as Benjamini–Schramm conclusions.

## 9. Relation to earlier work and verification semantics

The previous conversation's note `torsion-actions.md` proved a detour criterion under uniformly finite abelian centralizers, using finite-pattern approximation and paid repair. The present arguments retain paid repair, replace the pattern theorem by finite-partition derandomization, stop detours at their first subgroup return, and absorb centralizer collisions.

Donoso-Echenique and Silva [DS] provide relevant recent torsion-cycle ideas and prove that sufficiently large odd free Burnside groups have **infimal group cost** one. Their article explicitly distinguishes that statement from fixed price one. Their theorem is neither contradicted nor upgraded to the odd-exponent fixed-price assertion here.

The associated finite replay checks multiplication tables, subgroup cosets, first-return words, the fiber identity, finite matching/centralizer counting, repaired connectivity for every labeling in selected finite models, and rational selector probabilities. It does not prove measurable selection, infinite subgroup closure, cost lower bounds, Held's theorem, or the Burnside embedding results. Those steps are supplied by the written arguments and the cited sources.

Cairn's ESTABLISHED status records that a claim has an asserted complete written proof route or a cited imported theorem. It is not external mathematical validation or formal proof checking. Both universal problem nodes remain OPEN; earlier files are retained as provenance and are not all independently re-audited by this continuation.

## References

[G] Damien Gaboriau, *What is... cost?*, arXiv:1011.2294. Standard definitions, finite-group cost, and the infinite-action lower bound. https://arxiv.org/html/1011.2294v1

[H] Dieter Held, *On abelian subgroups of an infinite 2-group*, Acta Scientiarum Mathematicarum (Szeged) 27 (1966), 97–98. The theorem on page 97 states that an infinite 2-group contains an infinite abelian subgroup. Original publisher scan: https://acta.hu/download.phtml?id=859

[I] Sergei V. Ivanov, *On the Burnside Problem for Groups of Even Exponent*, Documenta Mathematica, Extra Volume ICM 1998, II, 67–75. In particular the standing exponent assumptions and Theorem 1 on page 68, and Theorem 3 and its corollary on pages 71–72. https://ems.press/content/book-chapter-files/27136

[IO] Sergei V. Ivanov and Alexander Yu. Olshanskii, *On finite and locally finite subgroups of free Burnside groups of large even exponents*, Journal of Algebra 195 (1997), 241–284. The pertinent statements were verified through the author's primary-source summary [I]. https://doi.org/10.1006/jabr.1996.6941

[DS] Miguel Donoso-Echenique and Eduardo Silva, *Free Burnside groups of large odd exponent have cost 1*, arXiv:2608.20472v1, August 20, 2026. Theorem 1.2 concerns infimal group cost; its following paragraph explicitly does not assert fixed price one. https://arxiv.org/html/2608.20472v1

Prior conversation source: `fixed-price-percolation-torsion-actions.md`, especially Sections 2–4. Its centralizer hypothesis is removed in Theorem 4.1 of this note. None of the previous unresolved universal estimates is used as a proved input.
