# A torsion-free fixed-price-one construction, a non-Hopfian example, and local connected sparsifiers

Research continuation — September 9, 2026

## Status and boundaries

This note supplies written deductions from explicitly stated classical inputs. It does not prove universal Fixed Price or universal Benjamini–Schramm. No originality, independent referee approval, or formal verification is claimed. The prior broad bounded-exponent and two-generator claims are not used. The finite-priority lemma needed here is reproved.

The substantive extension is that torsion is not required: non-power relators with a bounded number of occurrences of a distinguished generator supply arbitrarily many disjoint alternatives. We obtain an explicit torsion-free, nonamenable, non-Hopfian group with fixed price one. For its standard Cayley graph, an explicit finite-radius function of iid finite-valued labels always gives a connected spanning graph and has expected degree arbitrarily close to two. The nonuniqueness-percolation conclusion is an application of published theorems, not a new percolation proof.

## 1. Presentation and main conclusions

For i>=1 define the positive cyclically reduced word

    r_i = product_{j=1}^{13} a b^(100 i+j),
    |r_i| = 1300 i+104.

For any infinite J subset {1,2,...}, put

    G_J = <a,b | r_i=1 for i in J>.

**Theorem A.** Every G_J is torsion-free, contains the explicitly specified free subgroup <a^2,b^2> isomorphic to F_2, and has fixed price one. For every essentially free p.m.p. action alpha, every finite set of k distinct indices in J, and every eta>0, there is a measurable U such that

    {T_b on X, T_a restricted to U}

is a generating graphing and

    mu(U) <= I_k+eta,
    I_k = integral_0^1 (1-t^12)^k dt
        = product_{j=1}^k 12j/(12j+1)
        <= k^(-1/12).

Every G_J is infinitely presented. The infinite subsets J give continuum many marked groups and therefore continuum many unmarked isomorphism types.

Let G=G_N (all positive indices).

**Theorem B.** The endomorphism

    Phi(a)=a b^100,       Phi(b)=b

of G is surjective and not injective. The explicit word

    r_0 = product_{j=1}^{13} a b^j

is nonidentity in G, satisfies Phi(r_0)=1, and is killed by every homomorphism from G to a finite group. In particular G is not residually finite.

**Theorem C.** For each k,M>=1, independent uniform labels xi(g) in {1,...,M} on G define a connected spanning subgraph H_(k,M) of Cay(G,{a,b}) as in Section 6. It is connected for EVERY labeling, not only almost surely. The a-edge at g is determined by labels at ambient distance at most 1200k+90 from g. Its exact expected degree is

    E deg_H(e) = 2+2 rho_(k,M),
    rho_(k,M) = (1/M) sum_{r=0}^{M-1} [1-(r/M)^12]^k,
    I_k <= rho_(k,M) <= I_k+1/M.

Every original a-edge has a replacement path of length at most

    D_(k,M) = 12^(M-1) + (1300k+91)(12^(M-1)-1)/11.

Thus finite radius and a deterministic finite connectivity certificate coexist with arbitrarily small expected degree excess above two. Neither a connected limit nor a graphing attaining cost exactly one is asserted.

## 2. Imported mathematical inputs

[G] supplies the definitions of graphing cost, the infinite-class lower bound one, and the fact that containing F_2 precludes amenability.

[S, Theorem 3.7] is Greendlinger's lemma: a nonempty reduced null word over a classical C'(1/6) presentation has a cyclic boundary segment containing more than half of a defining relator or its inverse. The statement applies to infinite presentations since a particular diagram uses finitely many relators.

[GS, Section 1.1 and Section 2.2] recalls that graphical C(7) presentations without label-preserving symmetries give torsion-free groups. In the classical case, a C'(1/6) presentation with no relator a proper power satisfies this condition. This is the only imported torsion-freeness theorem needed here.

[GS, Lemmas 2.15 and 2.17] says that finite relator circles in the graphical Gr'(1/6) case embed isometrically and convexly in the Cayley graph, and images of any two components have connected or empty intersection. We use the intersection statement for circles placed at the identity. Since it is an intersection of actual subgraphs, a shared starting vertex has its unique outgoing a-edge in both circles when that vertex precedes an a in both words.

[GS, Theorem 1.3] and [CS] supply the optional percolation consequence in Section 9.

No theorem identifying the maximum-cost action is used in the fixed-price proof: the construction takes place in every specified free action.

## 3. Algebraic checks

### 3.1 Small cancellation and absence of proper powers

All b-run lengths 100i+j, with i>=1 and 1<=j<=13, are distinct as pairs (i,j) vary. A common segment of two essentially different cyclic relator occurrences cannot contain two a-letters. Otherwise the complete b-run between successive a-letters identifies its unique occurrence; alignment of that run and of the initial segment would make the occurrences identical. This covers distinct relators and distinct shifts of the same relator. The inverse cases are identical, while a positive relator and an inverse have no common letter.

Consequently every piece in r_i has length at most

    2(100i+13)+1 = 200i+27.

For i>=1,

    6(200i+27) = 1200i+162 < 1300i+104 = |r_i|,

since 100i>58. This proves C'(1/6) for the full family and every subfamily.

No r_i is a proper power in the free group. All thirteen b-runs have distinct lengths, whereas a repeated cyclic word would repeat its run pattern. Thus the disjoint union of the labeled relator circles has no nontrivial label-preserving automorphism on any component. The torsion-freeness input in Section 2 applies.

### 3.2 Infinite order and a free subgroup

A nonzero pure power of a or b cannot contain half a relator, so Greendlinger gives infinite order for both. Alternatively, their squares lie in the free subgroup below.

Substitute A=a^2 and B=b^2 into any nonempty cyclically reduced word in the abstract free generators A,B. The expanded cyclic word is freely reduced, and each of its nonempty maximal a-runs and b-runs has even length. A subword matching a positive r_i cannot pass through an internal a-run: the a-letters in r_i are isolated. Hence a match has at most two a-letters, only at its endpoints, with one b-run of length at most 100i+13 between them. Its length is at most 100i+15. The same holds for inverse relators, and a segment with no a is shorter still.

    2(100i+15) < 1300i+104.

Greendlinger therefore prevents such a word from being trivial. Conjugating an arbitrary nontrivial reduced A,B-word to a cyclically reduced one proves <a^2,b^2> is isomorphic to F_2. Thus G_J is nonamenable.

### 3.3 Disjoint twelve-point supports

For 1<=j<=12 set

    v_(i,j) = product_{ell=1}^j a b^(100i+ell),
    P_i = {v_(i,1),...,v_(i,12)}.

The embedded circle C_i labeled r_i has, before its thirteen a-edges, the vertices

    e, v_(i,1),...,v_(i,12).

Embedding makes these thirteen vertices distinct. In particular P_i has twelve elements and excludes e.

Place C_i and C_h, i!=h, at e. Their intersection contains the initial directed a-edge. By [GS, Lemma 2.17] it is connected. It is not an entire circle because the cyclic b-run patterns differ. A proper connected subgraph of a circle is a path. Such a common path has at most one a-edge: two would identify an intervening b-run length belonging to both relators, contrary to distinctness.

If w belonged to P_i intersect P_h, it would precede an a-edge in both circles. The outgoing a-edge at w would belong to the intersection, in addition to the outgoing a-edge at e. They are distinct because w!=e and a has infinite order. This is impossible. Therefore the P_i are pairwise disjoint.

### 3.4 Irredundancy and infinitely many groups

If r_h is omitted, the remaining presentation still satisfies C'(1/6). A matching segment between r_h and any remaining r_i has at most one a and length at most 200i+27, strictly less than half of r_i. Thus r_h is nontrivial in the omitted presentation by Greendlinger. More generally r_h is trivial in G_J exactly when h belongs to J.

Every defining relator is essential. If G_J had a finite presentation, the kernel of the epimorphism F(a,b)->G_J would be finitely normally generated. Each of those finitely many generators lies in the normal closure of finitely many defining relators, forcing a finite defining subfamily to generate the kernel. Irredundancy contradicts that. Thus G_J is not finitely presentable.

Different infinite subsets J give different marked groups, detected by r_h. There are continuum many such subsets, while each countable group has only countably many ordered generating pairs. Hence there are continuum many unmarked isomorphism types. This does not assert that the indexing by J is injective on unmarked types.

## 4. The finite-priority argument, without torsion

Let G_J act freely and p.m.p. on a standard probability space (X,mu). Remove an invariant null set, and write the action on the right. Keep T_b everywhere. These edges generate all b^m-connections, for every integer m, at graphing cost one.

For relator r_i, the tail after its first a is a valid path from xa back to x. It starts with b^(100i+1), then alternates the remaining twelve a-edges with the remaining b-runs. The new a-edges have starting points xv_(i,j), 1<=j<=12.

Fix k indices and a finite-valued measurable priority function r:X->{1,...,M}. Retain the a-edge at x exactly when

    for every selected index i,
    there is j in {1,...,12} with r(xv_(i,j))>=r(x).

Equivalently, delete it when some relator tail uses only a-edges with strictly smaller starting-point priorities.

**Preservation.** By induction on the priority value, every a-connection is recovered. At the lowest priority no edge is deleted because every candidate has nonempty support. At higher priority, a deleted edge has a path using only full b-connections and lower-priority a-edges; replace those edges by their already-recovered paths. There are only finitely many levels, and each candidate path is finite. Thus {T_b,T_a|U} generates the full action for every finite-priority assignment. Ties retain edges and never invalidate the induction.

**Cost.** Given eta>0, take a finite measurable partition separating the distinct points

    xg,  g in {e} union P_(i_1) union ... union P_(i_k),

outside a set of roots of measure below eta. Refining finite partitions separate points; freeness and a finite union bound justify the choice. Assign independent continuous uniform priorities to the finitely many atoms, then replace them by their finite ranks, which preserve all comparisons.

At a root outside the collision exception, conditional on its own original priority being t, the twelve tested points of each candidate are all lower with probability t^12. Different candidates use disjoint atoms. Hence the root's a-edge is retained with probability (1-t^12)^k. Averaging t, roots, and the finite atom randomization gives a deterministic ranking for which

    mu(U) <= integral_0^1(1-t^12)^k dt + eta.

Generation also holds at collision roots, where only the probability bound was lost. This proves the claimed graphing bound in Theorem A.

Let I_k denote the integral. Integrating the derivative of t(1-t^12)^k yields

    (12k+1)I_k=12k I_(k-1),    I_0=1,

so I_k=product_{j=1}^k 12j/(12j+1). Moreover

    I_k <= integral_0^infinity exp(-k t^12)dt
        = Gamma(13/12) k^(-1/12)
        <= k^(-1/12).

The last inequality follows from log-convexity between Gamma(1)=Gamma(2)=1; it can be proved directly by Holder on the defining gamma integrals. This estimate is not needed for convergence: dominated convergence already gives I_k->0.

Thus C(alpha)<=1 for every alpha, and the infinite-class lower bound supplies equality. The graphings are constructed separately for each k and eta. The numerical limit of their costs is not treated as a generating limit graphing.

## 5. An explicit surjective noninjective endomorphism

Here take J=N, so all positive-index relators are present. On the free group, the Nielsen automorphism

    phi(a)=a b^100,       phi(b)=b

satisfies phi(r_i)=r_(i+1). It therefore descends to an endomorphism Phi of G. It is surjective: b is in its image and Phi(a b^(-100))=a.

The positive word r_0=product_(j=1)^13 a b^j has length 104. Every defining relator has length at least 1404. Therefore r_0 has no relator-half segment and is nontrivial by Greendlinger. But Phi(r_0)=r_1=1. This proves non-Hopfianity, meaning a surjective endomorphism that is not an automorphism.

There is also a direct finite-quotient obstruction. Let f:G->Q be a homomorphism to a finite group, and let d be the order of f(b). Since r_d=1 and f(b)^(100d)=1,

    f(r_0) = product_j f(a)f(b)^j
           = product_j f(a)f(b)^(100d+j)
           = f(r_d)=1.

The explicitly nonidentity r_0 is invisible in every finite quotient. Thus G is not residually finite. This conclusion is proved directly, without an appeal to the general Hopfian theorem for finitely generated residually finite groups.

One may define r_i by the same word formula for all integer i, with negative powers reduced. For each k>=1, Phi^k(r_(1-k))=r_1=1 while Phi^(k-1)(r_(1-k))=r_0!=1. Thus the ascending kernel chain ker(Phi^k) is strictly increasing. This does not establish differing costs of any free actions: actions pulled back through Phi have nontrivial kernel and are not free.

## 6. A finite-radius connected graph from finite-valued iid labels

Again use J=N. Fix integers k,M>=1. Give every vertex g of the standard Cayley graph an independent uniform label xi(g) in {1,...,M}. Keep every unoriented b-edge. Keep the a-edge {g,ga} iff

    for every i in {1,...,k},
    at least one j in {1,...,12} has xi(gv_(i,j))>=xi(g).

This is an equivariant function of the labeled Cayley graph. Its connectivity proof is the deterministic finite-priority induction in Section 4, applied to the vertices of the group itself. It works for every labeling, including constant labelings. No global choice or measurability approximation is needed.

The word length of v_(i,j), using its positive spelling, is

    100ij+j(j+3)/2.

In particular |v_(i,12)|<=1200i+90. Thus the decision at an oriented a-edge starting at g uses only labels in the radius-(1200k+90) ball at g. To decide every incident edge at g at once, radius 1200k+91 suffices (for the incoming a-edge). This is a finite-radius, or block, factor of iid; the mathematical definition does not require choosing a canonical word form algorithm.

Conditional on xi(g)=r+1, each other tested point has a smaller label with probability r/M. Distinctness of e and all supports gives

    P(a-edge retained) = rho_(k,M)
        = (1/M) sum_(r=0)^(M-1) [1-(r/M)^12]^k.

This is a decreasing-function left Riemann sum. Consequently

    I_k <= rho_(k,M) <= I_k+1/M <= k^(-1/12)+1/M.

The difference estimate follows by sandwiching with the right Riemann sum; their difference is exactly (f(0)-f(1))/M=1/M.

There are always two b-edges at a vertex. The incoming and outgoing a-edge each have retention probability rho_(k,M). The generating edges are distinct because <a^2,b^2> is free. Hence

    E deg_H(e)=2+2 rho_(k,M).

For 0<epsilon<1, choose

    k=ceil((4/epsilon)^12),       M=ceil(4/epsilon).

Then E deg_H(e)<=2+epsilon. Each fixed choice produces a genuinely connected spanning subgraph of the original degree-four Cayley graph.

### An explicit bound on replacement distances

The tail of r_i has twelve a-edges and total b-length 1300i+91. Let B=1300k+91. A retained a-edge has length-one replacement; at priority level r>1 a deleted edge can be replaced using at most twelve lower-priority a-connections and B b-steps. Thus

    D_1=1,        D_r=B+12D_(r-1),
    D_M=12^(M-1)+B(12^(M-1)-1)/11.

For every labeling, every original a-edge has a replacement path of length at most D_M. Every b-edge remains. Therefore

    d_G(u,v) <= d_H(u,v) <= D_M d_G(u,v).

The bound is enormous as the target degree excess tends to zero, but finite for each construction. It does not contradict earlier detour-length obstructions, which prohibited uniform metric bounds as cost approaches one. No claim of connectivity at the limiting value of the parameters is made.

## 7. Optional realization notes

An algorithm specifying the output on a root's outgoing edge needs only the finite list of words v_(i,j) and the labels reached by those words. The independent vertex labels must be assigned to group elements, not to syntactically distinct words; the disjoint-support theorem proves that the particular tested words give distinct vertices. Assigning independent labels to all words would define a different, generally inconsistent model.

For an arbitrary free p.m.p. action, independent vertex labels are not assumed. Section 4 uses a finite partition and averaging on the original action space. The local iid construction and the arbitrary-action graphing proof are separate implementations of the same deterministic rule.

## 8. Further class-level deductions

Every G_J has a countable presentation with two generators and infinitely many indispensable relators. Any prescribed finite radius R can be made free-tree-like by choosing J in a sufficiently far tail: if every relator has length >4R+2, Greendlinger excludes nontrivial null words of length <=2R+1, which excludes vertex and edge identifications in the radius-R Cayley ball.

For the full-tail presentations J={I,I+1,...}, the groups are in fact isomorphic as unmarked groups, by the automorphism phi^(I-1) of F(a,b). Thus one may regard the large-free-ball phenomenon here as a family of markings of the same abstract fixed-price-one group. This observation does not reverse the noninjectivity of the endomorphism in Section 5: the isomorphism changes the target defining normal subgroup, whereas Phi is a map of one fixed quotient to itself.

## 9. Percolation and the unresolved universal goals

By [GS, Theorem 1.3], the classical C'(1/6) presentations above yield virtually cyclic or acylindrically hyperbolic groups. The explicit F_2 subgroup excludes virtual cyclicity. Applying [CS] gives p_c<p_u on every locally finite Cayley graph of every G_J. This is an imported class theorem after verifying the algebraic hypotheses, not a new proof of universal Benjamini–Schramm.

Fixed Price is established above for these explicit groups, but not for every countable infinite group. Torsion is no longer the essential resource; the construction still requires infinitely many relator tails with disjoint sets of required new edges. Arbitrary groups need not have this geometry. There is no established transport theorem comparing arbitrary actions of all groups, and no universal near-critical percolation estimate here.

The noninjective endomorphism does not produce a Fixed Price counterexample. Pullback through its nontrivial kernel fails the required freeness. Both universal goals remain OPEN.

## 10. Finite verification

The accompanying standard-library-only script verify.py has executable exact checks for:

- all positive cyclic rotations of the first five non-power relators, using suffix sorting and adjacent longest-common-prefix comparisons to compute each rotation's largest overlap; inverse cases have the same statistics and mixed signs no overlap;
- formal substitutions phi(r_i)=r_(i+1), relator lengths, support radii, and the short kernel-word bound;
- every three-valued priority labeling on all partitions of four- and five-point cyclic actions, and every binary labeling on all partitions of a six-point cyclic action; candidates enumerate minimal supports of actual finite connecting paths;
- strict-priority probability integrals, tied-priority probabilities, exact rational product formulas, Riemann-sum bounds, and route-length recurrences;
- finite permutation-group checks of the periodicity identity proving every finite quotient kills r_0.

The recorded run passes 68,833 exact assertions, including 26,843 simultaneous-deletion labelings. These finite checks do not prove the infinite small-cancellation, torsion-freeness, relator-circle embedding, measurable-selection, or cost assertions. In particular finite quotients cannot witness the nontriviality of r_0: the mathematical argument proves that they all kill it. The finite test count is not evidence of a formally verified solution to either conjecture.

Cairn verifies identifiers, artifacts, and dependencies, not mathematical truth. New established statuses encode an asserted written proof or an explicitly imported theorem. Earlier files are retained as provenance and not re-certified by this continuation.

## References

[G] Damien Gaboriau, *What is... cost?*, arXiv:1011.2294v1 (2010). We use definitions and the infinite-class lower bound, not the displayed compression formula in that short article. https://arxiv.org/html/1011.2294v1

[S] Mark Sapir, *Asymptotic invariants, complexity of groups and related problems*, arXiv:1012.1325v4, Theorem 3.7 (Greendlinger lemma). https://arxiv.org/html/1012.1325v4

[GS] Dominik Gruber and Alessandro Sisto, *Infinitely presented graphical small cancellation groups are acylindrically hyperbolic*, arXiv:1408.4488v3 (2016). Section 1.1 (torsion-free graphical C(7)), Definition 2.3, Lemmas 2.15 and 2.17 (convex embedding and connected intersections), and Theorem 1.3. https://arxiv.org/html/1408.4488v3

[CS] Inhyeok Choi and Donggyun Seo, *Percolation in acylindrically hyperbolic groups*, arXiv:2508.08932v2 (2025). https://arxiv.org/abs/2508.08932

Prior conversation note: *Finite-priority deletion and composite-order fixed-price-one groups*, fixed-price-finite-priority.md. This continuation reproves the finite-priority principle and removes torsion from the new explicit family.
