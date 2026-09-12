# Explicit fixed-price-one groups from abundant torsion detours

Research continuation — September 9, 2026

## Status, attribution, and scope

This note gives an explicit family of two-generated, nonamenable, infinitely presented groups for which every essentially free probability-preserving action has cost one. The specified torsion orders can tend to infinity. The construction yields continuum many isomorphism types and can be arranged to have any prescribed finite Cayley ball equal to the corresponding ball in the free group of rank two.

The proof combines a finite measurable selection-and-repair argument with classical small-cancellation theory. The earlier conversation's variable-order repair criterion anticipated one part of the method; the actual group construction and all needed algebraic checks are supplied here. No earlier broad bounded-exponent, two-generator, or Burnside cost claim is assumed.

The percolation conclusion for this family is an application of Gruber–Sisto and Choi–Seo, not a new proof of the universal Benjamini–Schramm conjecture. The two universal conjectures and the earlier fixed-exponent free Burnside target remain OPEN. These are written deductions, not independently refereed or formally verified results; no originality or priority is claimed. Finite replay checks test finite identities, not infinite theorem validity.

## 1. Main statement

Let I>=1. For every integer i>=I choose a prime p_i>=13. Suppose

    sum_{i>=I} q^(p_i-1) = infinity       for every 0<q<1.        (1.1)

Define

    G(p,I) = < a,b | (a b^i)^(p_i)=1, for every i>=I >.          (1.2)

**Theorem 1.** The following statements hold.

1. The presentation is classical C'(1/6), with its symmetrized relator set treated as a SET of distinct words. Proper powers are allowed.
2. a and b have infinite order, <a^2,b^2> is a free subgroup of rank two, and G(p,I) is nonamenable.
3. Each a b^i has exact order p_i; the cyclic subgroups <a b^i> have pairwise trivial intersection.
4. In every essentially free p.m.p. action on a standard probability space, and for every epsilon>0, there is a measurable set A with mu(A)<epsilon such that the two partial transformations

       T_b on X,          T_a restricted to A

   generate the whole orbit relation. In particular every such action has cost exactly one.
5. G(p,I) is not finitely presentable. The intersection <b> intersect a<b>a^(-1) is trivial, even though the relative cost above the <b>-relation is zero in every free action.
6. G(p,I) is acylindrically hyperbolic by [GS]. Consequently, by [CS], Bernoulli bond percolation on every locally finite Cayley graph of G(p,I) has a nonuniqueness interval: p_c<p_u.

A sufficient condition for (1.1) is

    p_i = o(log i).                                             (1.3)

The sequence in (1.3) can tend to infinity. Thus neither the group nor the prescribed family of detours needs bounded exponent.

Items 1–5 are proved in Sections 2–5 below. Item 6 is explicitly separated as an application of external theorems in Section 7.

## 2. Finite measurable repair, with every exception paid for

### 2.1. Definitions

Let a countable group Gamma=<H,a> act essentially freely and probability-preservingly on a standard probability space (X,mu). Discard an invariant null set so that the action is free and use right notation x -> xg. Write R_H and R_Gamma for the orbit relations.

A graphing is a countable family of partial measure-preserving bijections. Its cost is the sum of their domain measures. Relation cost is the infimum over generating graphings. For S<=R,

    relC(R;S)=inf { C(Psi) : S joined with R_Psi equals R }.

Every added map below is a restriction of T_a. The standard cost lower bound for aperiodic relations is one [G]. Infima need not be attained; the construction below makes a different generating graphing for each positive error tolerance.

### 2.2. Finite detour lemma

Suppose b_1,...,b_k belong to H and

    c_i=a b_i,   ord(c_i)=d_i>=2,
    P_i={c_i,c_i^2,...,c_i^(d_i-1)}

are pairwise disjoint sets of group elements. For every 0<q<1 and eta>0, there is a measurable A such that

    R_H joined with R_(T_a|A) = R_Gamma,
    mu(A) <= q+(1-q) product_{i=1}^k(1-q^(d_i-1))+eta.          (2.1)

**Proof.** Let F={e} union P_1 union ... union P_k. Refining finite measurable partitions separate points in a standard Borel model of X. For g!=h in F, freeness implies xg!=xh almost surely, so the probability that these two points remain in the same partition atom tends to zero. There are finitely many pairs. Choose a finite partition for which the roots with any tested collision have measure less than eta.

Temporarily color its finitely many atoms selected with probability q, independently. Let U be their union. For a root x, a detour i succeeds when xc_i^j belongs to U for every 1<=j<d_i. Define D(U) to be the roots where every detour fails, and A(U)=U union D(U).

At a root outside the collision exception, the coordinate labels are independent. The detour supports are disjoint, and the identity is in none of them. Therefore

    P_colors(x in A(U))
       = q+(1-q) product_i(1-q^(d_i-1)).                        (2.2)

At other roots use the upper bound one. Integrating (2.2) and averaging over the finite coloring probability space gives a deterministic measurable choice of U for which the measure bound in (2.1) holds.

It remains to verify generation, which holds for EVERY coloring, not merely on the roots with distinct atom labels. If x is in D(U), its direct a-edge is retained. Otherwise choose a successful i. Starting at xa, use

    xa --b_i--> xc_i --a--> xc_i a --b_i--> xc_i^2
       --a--> ... --b_i--> xc_i^(d_i)=x.                        (2.3)

All b_i-steps are R_H-connections. Every displayed a-step starts in U. Thus x is connected to xa in the joined relation. Since Gamma=<H,a>, this joined relation is the entire orbit relation. All its edges are already in R_Gamma, so there is no overshoot. QED.

The proof selects a set on the original action space. It does not replace the action by a Bernoulli extension. It controls the union of selected and repaired domains, and does not require paths inside R_H to have uniformly bounded lengths.

### 2.3. Infinite families and an abundance threshold

Suppose an infinite family satisfies the same pairwise-disjointness condition. If

    sum_i q^(d_i-1)=infinity,

then product_{i<=k}(1-q^(d_i-1)) tends to zero, so (2.1) yields relC(R_Gamma;R_H)<=q. In particular, divergence for every q>0 gives

    relC(R_Gamma;R_H)=0.                                      (2.4)

For each epsilon the argument chooses q, then finite k, then a finite partition. No connectedness assertion is made about a limiting graphing.

More quantitatively, define

    q_* = inf { q in (0,1] : sum_i q^(d_i-1)=infinity }.

Then relC<=q_*, where q_*=1 is covered by retaining T_a everywhere. If H admits a graphing of cost c in the given action, C(R_Gamma)<=c+q_*.

If N(R)=#{i:d_i-1<=R} is finite for every R, put

    h=limsup_{R->infinity} log N(R)/R.

Then

    q_*=exp(-h),       with exp(-infinity)=0.                    (2.5)

To prove this, write q=exp(-t). If t<h, choose t<alpha<h. Along infinitely many R, N(R)>=exp(alpha R), and the partial sum over d_i-1<=R is at least exp((alpha-t)R); hence it diverges. If t>h, choose h<alpha<t; eventually N(R)<=exp(alpha R). Group the terms by their integer lengths to bound the series by a convergent geometric series. The boundary value does not affect the infimum. If N(R) is infinite for some finite R, divergence holds for every q>0 directly.

This identifies the relevant balance: how many disjoint detours are available versus how many selected edges each requires.

## 3. Small cancellation and algebra of the concrete presentation

Write

    u_i=a b^i,          r_i=u_i^(p_i),          |r_i|=p_i(i+1).

Symmetrize by taking all cyclic shifts of the r_i and their inverses, and remove duplicate WORDS. Rotations by a whole period of a proper power are identical words, not different relators for purposes of the classical piece condition.

### 3.1. Piece bound

A piece is a common initial segment of two distinct words in that symmetrized set. Equivalently, we examine common segments with fixed starting positions in periodic relator words.

If the two words come from different indices i!=j, a common positive segment has at most one occurrence of a: two consecutive a's in r_i are separated by exactly i b's, whereas in r_j they are separated by j b's. Thus a piece in r_i has length at most 2i+1; more symmetrically it has length at most 2 min(i,j)+1. The same argument applies to inverse words. A positive relator and a negative inverse relator share no letter.

If the two words are distinct cyclic shifts of the SAME r_i, a shared segment containing an a would align their phases modulo i+1 and make the entire shifted words identical. That case was removed in forming the set. Hence their common segment contains only b's and has length at most i. The inverse case is the same.

Consequently every piece u in a symmetrized r_i obeys

    |u| <= 2i+1 < p_i(i+1)/6,                                 (3.1)

because p_i>=13. The presentation is C'(1/6).

We use the classical Greendlinger lemma: in a reduced nonempty null word, some cyclic boundary segment contains more than half of a cyclic shift of a defining relator or its inverse [S, Theorem 3.7]. The theorem applies to infinite presentations as well: a van Kampen diagram uses only finitely many relators, and that finite subpresentation still satisfies C'(1/6). Proper-power relators are permitted in the classical symmetrized-set version being used here.

### 3.2. Infinite order and nonamenability

Every nontrivial power of b has no a-letter, so it cannot contain more than half of any r_i or inverse. Greendlinger implies b has infinite order. The same argument, or the free-subgroup argument next, gives infinite order for a.

Take a nonempty cyclically reduced word W in two abstract generators A,B, and substitute

    A=a^2,        B=b^2.

The resulting cyclic word is freely reduced. Its maximal a-runs and b-runs have nonzero even lengths. A segment matching a positive r_i cannot pass through an internal a-run, because every a in r_i is isolated by b's. Therefore any such matching segment has at most two a-letters, which can occur only at its ends, with one b-run of length at most i between them. Its length is at most i+2. A segment with no a has length at most i. The same bounds apply to inverse relators.

Since

    i+2 < p_i(i+1)/2,

no such word contains a relator half. Greendlinger shows that it is nontrivial. Every nontrivial reduced A,B-word is conjugate to a nonempty cyclically reduced one, so

    <a^2,b^2> is isomorphic to F_2.                            (3.2)

In particular G(p,I) is nonamenable and infinite. This uses only the usual fact that subgroups of amenable groups are amenable and F_2 is not amenable.

### 3.3. Exact prescribed orders

The word u_i=a b^i is nontrivial. It has only one positive a on its cyclic boundary, so it cannot contain more than half of any r_j or inverse (a segment with at most one a has length at most 2j+1, which is far shorter than half of r_j). Greendlinger applies.

The relation u_i^(p_i)=1 and primality of p_i then give

    ord(u_i)=p_i.                                             (3.3)

No general torsion-classification theorem for small-cancellation groups is required.

### 3.4. Pairwise disjoint power sets

If p_i!=p_j, the prime-order cyclic subgroups <u_i>,<u_j> have trivial intersection.

If p_i=p_j=p and the intersection is nontrivial, both subgroups have order p and must coincide. Thus

    b^(j-i)=u_i^(-1)u_j

belongs to a finite group. Since i!=j, this contradicts infinite order of b. Hence the cyclic subgroups have pairwise trivial intersection in every case, and

    P_i={u_i,...,u_i^(p_i-1)}

are pairwise disjoint.

## 4. Proof of fixed price one

Fix ANY essentially free p.m.p. action alpha of G(p,I). Let H=<b>, which is infinite cyclic. The full transformation T_b is a graphing of R_H of cost one.

Apply the finite detour lemma with b_i=b^i, c_i=ab^i, and d_i=p_i. For finite k (using the first k indices beginning at I), any 0<q<1 and eta>0, it gives a measurable A such that {T_b,T_a|A} generates R_G and

    C({T_b,T_a|A})
       <=1+q+(1-q) product_{i=I}^{I+k-1}(1-q^(p_i-1))+eta.     (4.1)

Condition (1.1) implies that the product tends to zero for each fixed q>0. For epsilon>0 choose q<epsilon/3, then a finite k with product<epsilon/3, then eta<epsilon/3. This gives mu(A)<epsilon and a generating graphing of cost below 1+epsilon.

Thus C(alpha)<=1. The aperiodic-action lower bound [G] gives C(alpha)>=1. Since alpha was arbitrary,

    C(alpha)=1 for every free p.m.p. action of G(p,I).          (4.2)

The proof does not require ergodicity, does not use Bernoulli maximality, and does not compare unknown numerical invariants. Every epsilon has a complete generating graphing. It does not claim that a graphing of cost exactly one attains the infimum.

## 5. Additional algebraic structure

### 5.1. The cyclic subgroup does not have a large intersection with its a-conjugate

If <b> intersect a<b>a^(-1) contained a nonidentity element, infinite order of b would give integers m,n!=0 with

    a b^m a^(-1) b^(-n)=1.

This cyclically reduced word has one positive a and one negative a. A segment matching a positive relator has at most one positive a, and a segment matching an inverse relator has at most one negative a. Such segments have length at most 2i+1 relative to r_i, shorter than half its length. Greendlinger gives a contradiction.

Thus

    <b> intersect a<b>a^(-1)={e},

while Section 4 proves relC(R_G;R_<b>)=0 for every free action. This rules out an explanation based simply on infinite intersection for this one adjoining generator. It does not assert the absence of every other known fixed-price mechanism.

### 5.2. Every defining relator is essential; no finite presentation exists

Omit r_j from the presentation. Every other relator still satisfies C'(1/6). A nonempty word u_j^k has period j+1. A common segment with r_i, i!=j, has at most one a, so its length is at most 2 min(i,j)+1, less than half of r_i. Greendlinger shows u_j has infinite order in the omitted presentation.

In particular r_j is not in the normal closure of all other relators. The defining set is irredundant.

If G(p,I) were finitely presentable, the kernel of the map from F(a,b) to G(p,I) would be finitely normally generated. Each member of a finite normal generating set is a product of finitely many conjugates of the r_i and their inverses. A finite collection of the r_i would therefore normally generate the entire kernel, contradicting irredundancy. Thus G(p,I) is not finitely presentable.

## 6. Fully specified profiles, continuum many groups, and large free balls

### 6.1. An explicit profile with unbounded torsion orders

Let s_1=13<s_2=17<s_3=19<... enumerate the primes at least 13. Put

    M_j=2^(s_j^2).

For 1<=i<M_1 let p_i=13. For M_j<=i<M_(j+1), let p_i=s_j. Then p_i tends to infinity and, for i>=M_1,

    p_i <= sqrt(log_2 i) = o(log i).

For any q in (0,1), the latter estimate implies that eventually

    q^(p_i-1) >= i^(-1/2).

The series in (1.1) therefore diverges. This completely specified group has fixed price one, an explicit free subgroup, and finite-order elements with orders tending to infinity. The enormous block sizes are harmless for the mathematical definition; no prime-distribution estimate is needed.

### 6.2. Continuum many isomorphism types, all with unbounded torsion orders

Pair the primes as (s_(2j-1),s_(2j)) and put

    M_j=2^(s_(2j)^2).

For each binary sequence epsilon=(epsilon_j) choose p_i=s_(2j-1+epsilon_j) throughout M_j<=i<M_(j+1), and put p_i=13 in the finite initial block. Every resulting profile still tends to infinity and satisfies p_i=o(log i).

Different binary sequences give different MARKED groups (G,a,b), since the exact order of ab^(M_j) recovers the choice in block j. There are continuum many binary sequences. A countable finitely generated abstract group has only countably many ordered generating pairs, so one unmarked isomorphism type accounts for at most countably many of these markings. Therefore the family contains continuum many pairwise nonisomorphic groups, all satisfying Theorem 1 and having unbounded torsion orders.

This is a cardinality deduction, not an assertion that a particular naming of the groups is injective on unmarked isomorphism types.

### 6.3. Arbitrarily large free Cayley balls

All arguments apply after omitting any finite initial set of relators, i.e. using i>=I, since divergence is unaffected. Every remaining relator has length at least 13(I+1).

Fix R>=1 and choose I such that

    13(I+1)>4R+2.

If a nonempty freely reduced word of length at most 2R+1 were trivial, its cyclic reduction would also be nonempty and of that length or less, and Greendlinger would require it to contain a segment of length greater than 13(I+1)/2>2R+1, impossible.

It follows that the induced radius-R marked Cayley ball for {a,b} is exactly the radius-R ball of the four-regular free Cayley tree: vertex identifications would yield a relation of length at most 2R, and an extra edge would yield one of length at most 2R+1.

Nevertheless every free action has cost one, whereas free F_2 actions have cost two [G]. Thus within this explicit nonamenable family, no prescribed finite Cayley ball forces the global action-cost value. This is not claimed as a new general continuity theorem or a counterexample to an unasserted semicontinuity property.

## 7. Percolation for the constructed family: an imported consequence

Gruber–Sisto [GS, Theorem 1.3] proves that a classical C(7) group is virtually cyclic or acylindrically hyperbolic; classical C'(1/6) satisfies that hypothesis. Our groups contain F_2, so they are not virtually cyclic. Therefore they are acylindrically hyperbolic.

Choi–Seo [CS] proves that Bernoulli bond percolation on every Cayley graph of an acylindrically hyperbolic group has a nonuniqueness phase. In particular, for every locally finite Cayley graph C of every group constructed above,

    p_c(C)<p_u(C),

and parameters between those thresholds have infinitely many infinite clusters almost surely.

This means that both affirmative outcomes hold for this constructed family. The cost proof is in Section 4; the percolation conclusion is an application of the two named external theorems. No universal percolation theorem is proved here. The nonuniqueness interval is not numerically bounded by this note.

## 8. What this does not prove

These groups are not the fixed-exponent free Burnside groups from the preceding notes. They contain infinite-order elements, and the stronger profiles have unbounded torsion orders. We deliberately prescribe an abundance of particular torsion relations. Nothing here says that arbitrary groups, or the original large odd-exponent Burnside group, have the same usable detour supply above an infinite cyclic subgroup.

Universal Fixed Price asks for equality of all free-action costs of every countable group, including common values above one. The family theorem does not compare arbitrary actions outside the construction. Universal Benjamini–Schramm asks for every nonamenable Cayley graph; the acylindrically hyperbolic application does not remove that restriction.

The earlier low-cost-seed network target is neither assumed nor solved. The present construction bypasses it by specifying relations that make a direct finite repair work. This supplies real examples realizing the variable-order criterion, not a proof of its universal hypothesis.

## 9. Finite checks and research-graph semantics

The standard-library script `scripts/replay_small_cancellation.py` checks finite symmetrized relator sets, including deduplication of identical proper-power rotations; strict C'(1/6) inequalities; even-run words for the free-subgroup test; and powers of omitted roots against remaining relators in finite lists.

It also exhaustively checks selected-and-repaired graphs on regular actions of the finite dihedral groups of orders 6,8,10,12. Those are finite models of the repair lemma, not approximations of the infinite groups constructed above. Independent finite support families test exact union probabilities for unequal detour lengths at rational selection probabilities.

The saved replay has 143,311 exact assertions, including 51,490 comparisons of different symmetrized relators, 9,856 cyclically reduced squared-generator words, and 5,440 repaired finite labelings. These checks do NOT prove Greendlinger's lemma, the general infinite word bounds, measurable selection, infinite cost infima, or the two external percolation-related theorems. The written proofs and cited inputs address those steps.

Cairn tracks dependencies and artifacts. An ESTABLISHED label means that a written proof route or cited theorem has been entered, not that an automated prover or external referee verified it. The original universal goals remain OPEN. Earlier cumulative nodes are retained as provenance and are not all re-audited or assumed by this continuation.

## References

[G] Damien Gaboriau, *What is... cost?*, arXiv:1011.2294v1 (2010). Standard definition of graphing/action cost, the lower bound one for infinite free actions, and cost two for free F_2 actions.
https://arxiv.org/html/1011.2294v1

[S] Mark Sapir, *Asymptotic invariants, complexity of groups and related problems*, arXiv:1012.1325v4. Definition 3.6 and Theorem 3.7 state classical C'(lambda) and the Greendlinger lemma, with attribution to Lyndon–Schupp. We use the classical theorem, not a new proof of small cancellation theory.
https://arxiv.org/html/1012.1325v4

[GS] Dominik Gruber and Alessandro Sisto, *Infinitely presented graphical small cancellation groups are acylindrically hyperbolic*, arXiv:1408.4488v3; Annales de l'Institut Fourier 68(6) (2018), 2501–2552. Theorem 1.3 covers classical C(7), hence C'(1/6), presentations including proper-power relators.
https://arxiv.org/html/1408.4488v3
https://aif.centre-mersenne.org/articles/10.5802/aif.3215/

[CS] Inhyeok Choi and Donggyun Seo, *Percolation in acylindrically hyperbolic groups*, arXiv:2508.08932v2 (August 13, 2025). The abstract and principal theorem assert a nonuniqueness phase for Bernoulli bond percolation on every Cayley graph of an acylindrically hyperbolic group.
https://arxiv.org/abs/2508.08932

Earlier conversation provenance: `fixed-price-connector-capacity.md`, variable-order torsion criterion; `fixed-price-burnside-explicit-bound.md`, selected-domain union accounting. Their needed finite selection/path arguments are reproved above. No prior broad conclusion is taken as an axiom.
