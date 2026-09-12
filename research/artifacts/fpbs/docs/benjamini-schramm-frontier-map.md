# Benjamini–Schramm: the verified frontier, permanence, and a minimal open class

Lane `bs-permanence-frontier`, 2026-09-12. Target: `p_c(G) < p_u(G)` for every
Cayley graph `G = Cay(Gamma,S)` of every nonamenable finitely generated group,
the root `fpbs-benjamini-schramm-universal`. This note does four things:

1. lists what is proved, with the generating-set quantifier of each result;
2. separates results that look like threshold separation but are not;
3. records which permanence statements are actually available;
4. reduces the root to a minimal open class and isolates one crux that is
   uniform over a very large class of groups (Section 7).

**Sources.** Unless marked otherwise, statements were read on 2026-09-12 from
arXiv PDFs downloaded on MSI and converted to text with poppler. Nothing here
is refereed or formally verified.

## 1. Every-generating-set theorems (group classes)

These are the only results that carry the full quantifier "every Cayley graph".

| Class | Source | Scope | In Cairn |
| --- | --- | --- | --- |
| Nonamenable Gromov-hyperbolic | Hutchcroft arXiv:1804.10191 | every quasi-transitive graph in the class | `fpbs-hyperbolic-and-nonunimodular-nonuniqueness` |
| Not of fixed price one | Lyons arXiv:1109.5418 | every Cayley graph | `fpbs-non-fixed-price-one-has-nonuniqueness` |
| Acylindrically hyperbolic | Choi–Seo arXiv:2508.08932v2, Theorem A | every Cayley graph | `fpbs-sc-choi-seo` |

* **Choi–Seo, abstract (verified):** "Let G be an acylindrically hyperbolic
  group. We prove that Bernoulli bond percolation on every Cayley graph of G has
  a nonuniqueness phase". Along the way they prove `chi_p ≲ (p_c-p)^(-1)`,
  `p_c < p_(2->2)` and the triangle condition (Theorem B).
* **Lyons, abstract (verified):** for every finitely generated `Gamma`, either
  `Gamma` has fixed price, or each Cayley graph has infinitely many infinite
  clusters for some Bernoulli parameter. The proof in the paper is written for
  site percolation. The Cairn node records the bond version through the
  archive's own quantitative bound: a collapse forces maximal cost one.
* **Gaboriau, arXiv:math/0405458, abstract (verified):** nonuniqueness phase on
  unimodular transitive graphs admitting nonconstant harmonic Dirichlet
  functions. For Cayley graphs this is `beta_1^(2)(Gamma) > 0`, which already
  forces cost `> 1` and so is contained in the Lyons class.

Nonunimodular graphs (Hutchcroft arXiv:1711.02590) are a graph-level class.
They reach Cayley graphs only when `Aut(Cay(Gamma,S))` has a closed transitive
nonunimodular subgroup, as in the tree-projected nodes
`fpbs-tree-projected-translate-symmetric-nonunimodular` and
`fpbs-tree-projected-reversible-letter-nonunimodular`.

## 2. Graph-level and some-generating-set theorems

* **Spectral criterion.** Juschenko–Nagnibeda arXiv:1206.2183v3, Proposition 3,
  credited to Pak–Smirnova-Nagnibeda: `rho(Gamma,S) < 1/2` implies `p_c < p_u`.
  It follows from `p_c <= 1/(1+h)`, Mohar's `h >= d(1-rho)` and
  `p_u >= 1/(d rho)`.
* **Pak–Smirnova-Nagnibeda**, C. R. Acad. Sci. Paris 330 (2000) 495–500. Not on
  arXiv; the statement is quoted from Juschenko–Nagnibeda Theorem 4. For every
  nonamenable `Gamma` and symmetric `S` there is `k` with
  `p_c(Gamma,S^(k)) < p_u(Gamma,S^(k))`, where `S^(k)` is the `k`-th power of
  `S ∪ {e}` **as a multiset**, so the graph has many multiple edges.
* **Juschenko–Nagnibeda, abstract (verified).** A simple generating set with
  `p_c < p_u` exists if `Gamma` contains an infinite normal `N` with `Gamma/N`
  nonamenable. The same holds for every finitely generated group containing
  such a `Gamma`, which covers free Burnside groups `B(n,p)`, `n >= 2`,
  `p >= 665`. Their page 4 records the PSN observation that groups containing
  `F_2` have simple generating sets with `rho -> 0`. By their Proposition 7,
  property RD gives `rho(S^k) -> 0`.
* **Nachmias–Peres arXiv:1207.1480v2, Theorem 1 (verified).** For every
  `rho < 1` there is `L` such that every transitive graph with spectral radius
  at most `rho` and girth at least `L` has `p_c < p_u`.
* **Kozáková arXiv:math/0611668.** Computes `p_c` of free products from the
  factors' subcritical susceptibilities. It proves no `p_u` statement.

## 3. Results that look like separation but are not

* **Hutchcroft–Pan arXiv:2409.12283v1.**
  * *Definition 1.11 (verified):* an "obstacle to uniqueness" has no **unique**
    `Gamma`-infinite cluster at `p_u(Gamma;G)`. The paper states explicitly that
    zero clusters are allowed.
  * *Theorems 1.13–1.15 and Corollary 1.16 (verified)* prove this for three
    classes:
    * groups with an amenable wq-normal subgroup of exponential growth
      (lamplighters `L wr Gamma`, `SL_n(Z[x])`, Thompson's `F` and `T`);
    * nonamenable products `H x K`;
    * property (T) groups, and relative (T) with respect to an infinite
      wq-normal subgroup.

  None of these is threshold separation: `fpbs-pu-nonuniqueness-cannot-separate`.
  An earlier Cairn line said Theorem 1.13 "needs an amenable wq-normal subgroup
  of exponential growth" for BS. That theorem is about uniqueness **at** `p_u`
  and gives no `p_c < p_u` for any group.
* **Lyons–Schramm arXiv:math/9811170:** `p_u < 1` for every Cayley graph of an
  infinite Kazhdan group (Corollary 6.6) and for wreath products
  (Corollary 6.8). Not separation.
* **Hutchcroft–Pete arXiv:1810.11015v2, abstract (verified):** Kazhdan groups
  have cost 1, and "It remains open if they have fixed price 1." So a (T) group
  is either covered by Lyons, or is a fixed-price-one candidate. Which case holds
  is unknown.
* **Hutchcroft–Pan arXiv:2412.15895v1:** on `T x Z^d`, and more generally on a
  tree times an infinite amenable Cayley graph or the lamplighter on a tree,
  `p_(2->2) = p_u` and the Hausdorff dimension jumps at `p_u`. The gap on those
  graphs comes from nonunimodularity.
* **Mukherjee–Recke arXiv:2303.17429v3:** characterizes the Haagerup property
  and property (T) by invariant percolations. It gives no Bernoulli threshold
  separation.
* **New preprints.** lit-scout-2 found no 2025–26 preprint separating thresholds
  beyond these classes. arXiv API searches on 2026-09-12 ("percolation AND
  nonuniqueness", "percolation AND Cayley AND uniqueness") found none either.
  The newest hits: Chu 2608.06644, D'Achille–Grebík–Khezeli–Recke 2511.23317,
  Grebík–Recke 2504.02435.

## 4. Test groups against the known classes

"Class A" means having an infinite amenable wq-normal subgroup (Section 5.1).

| Group | AH | Price-one status | Class A | Every Cayley graph |
| --- | --- | --- | --- | --- |
| `F_2 x Z` | no (infinite center) | fixed price 1 | yes (center) | OPEN, Choi–Seo Q1.3; tree-projected subclasses settled |
| `F_2 x F_2` | no | fixed price 1 | yes (`{1} x <a>`) | OPEN, Q1.5, Q1.7 |
| braid groups `B_n`, `n >= 3`; Seifert-fibred with hyperbolic base | no | fixed price 1 | yes (center) | OPEN, Q1.6 |
| `SL_3(Z)` | no | cost 1 (Hutchcroft–Pete); fixed price not recorded here | yes, see below | OPEN |
| lamplighter `Z/2 wr F_2` | no | fixed price 1 | yes (lamp group) | OPEN |
| hyperbolic, relatively hyperbolic, MCG, rank-one CAT(0) | yes | – | – | proved |
| Tarski monsters, torsion-free Tarski monsters | no | not recorded | no | OPEN; in the residual class of Section 6 unless not of price one |

`SL_3(Z)` is in class A with `H = <e_12>`. Two elementary matrices `e_ij` and
`e_kl` commute when `j != k` and `i != l`. The commuting graph on the six `e_ij`
is connected: `e_12 – e_13 – e_23 – e_21` and `e_12 – e_32 – e_31`. Let
`H <= I < SL_3(Z)`. Some `e_ij` lies outside `I`. A path in the commuting graph
from `e_12` to it has an adjacent pair `x in I`, `y notin I`, and then
`y I y^(-1) ∩ I ⊇ <x>` is infinite.

## 5. Permanence

### 5.1 Class A is closed under the natural operations

Use the intermediate-subgroup definition: `H <= Gamma` is wq-normal when every
`H <= I < Gamma` has some `g notin I` with `g I g^(-1) ∩ I` infinite.

* **Transitivity.** Let `H` be wq-normal in `K` and `K` wq-normal in `Gamma`,
  and take `H <= I < Gamma`.
  * If `K ⊄ I`, then `H <= I ∩ K < K`, so some `g in K \ I` has
    `g(I∩K)g^(-1) ∩ (I∩K)` infinite, hence `gIg^(-1) ∩ I` infinite.
  * If `K <= I`, wq-normality of `K` gives the required `g`.
* **Overgroups.** If `Gamma` has an infinite wq-normal subgroup `N` and `N` is
  in class A, then `Gamma` is in class A, by transitivity. This covers infinite
  normal subgroups and finite-index overgroups: a finite-index subgroup is
  commensurated, hence s-normal, hence wq-normal.
* **Finite quotients.** Let `F` be finite normal and `pi : Gamma -> Gamma/F`,
  and take `pi(H) <= J < Gamma/F`. Then `H <= pi^(-1)(J) < Gamma`, so some
  `g notin pi^(-1)(J)` has `g pi^(-1)(J) g^(-1) ∩ pi^(-1)(J)` infinite. Its
  image lies in `pi(g) J pi(g)^(-1) ∩ J`, and a finite-to-one image of an
  infinite set is infinite.
* **Products** with an infinite factor: `fpbs-product-amenable-subgroup-wq-normal`.

### 5.2 Separation along a subgroup passes to every overgroup

See Section 7, (a) and (b). If a Cayley graph `G` of any finitely generated
`Gamma~` containing an infinite subgroup `I` satisfies `p_c(G) < p_c(I;G)`, then
`G` has a nonuniqueness phase. No normality or amenability of `I` is used.

### 5.3 What does not transfer

Thresholds are properties of one graph. No available argument moves
`p_c < p_u` between Cayley graphs of:
* commensurable groups;
* `Gamma` and `Gamma/F`;
* two generating sets of one group. This is Choi–Seo Question 1.2 (verified):
  "Is the existence of non-uniqueness phase a group-invariant?" They note that an
  affirmative answer together with Pak–Smirnova-Nagnibeda would settle BS. But
  PSN is a multigraph statement, so what is needed is a simple generating set
  with a gap: Juschenko–Nagnibeda's question.

The fibre machinery does not change this.
* `fpbs-fibre-summed-connectivity-operator` and the RD weighted bubble
  criterion move the L2 question to a positive convolution kernel `sigma_p` on a
  quotient.
* But `sigma_p` is not the connectivity function of any percolation on a Cayley
  graph of the quotient. These are reductions of one graph's problem, not
  transfers between groups.

The proved classes transfer only as group classes: hyperbolicity is invariant
under quasi-isometry, and the cost criterion is a group invariant.

## 6. Reduction to a minimal open class

Every nonamenable finitely generated `Gamma` falls in at least one of four
cases:
1. not of fixed price one: Lyons;
2. acylindrically hyperbolic: Choi–Seo;
3. an infinite amenable wq-normal subgroup `H` exists: then, on each Cayley
   graph, `p_c < p_u` is equivalent to `E_p|K_o ∩ H| < infinity` for some
   `p > p_c` (`fpbs-bs-iff-finite-relative-susceptibility`);
4. otherwise: fixed price one, not acylindrically hyperbolic, and no infinite
   amenable wq-normal subgroup.

Case 4 is the **residual class**. By definition, each infinite amenable subgroup
of such a group lies in a proper subgroup `I` with `gIg^(-1) ∩ I` finite for
every `g notin I`. The known candidates are torsion or monster-like: Tarski
monsters, and torsion-free Tarski monsters, whose proper subgroups are cyclic
and whose maximal cyclic subgroups are almost malnormal. Whether they have
fixed price one is not recorded.

So the open part of the conjecture is case 3's analytic premise plus the
residual class. The smallest case-3 barometers already on the graph are the
tree-projected Cayley graphs of `F_n x Z` with mismatched decorations.

## 7. The thin-subgroup crux

Throughout, `G = Cay(Gamma,S)` is nonamenable, `I <= Gamma` is an infinite
subgroup, `p_c(I;G)` and `p_u(I;G)` are Hutchcroft–Pan's relative thresholds,
and `chi^I_p = E_p|K_o ∩ I|`.

**(a) `p_c(I;G) <= p_u(I;G) <= p_u(G)` for every infinite subgroup `I`.**
Take `p > p_u(G)`. There is a unique infinite cluster (uniqueness monotonicity),
so Hutchcroft–Pan Theorem 1.4 with `H = Gamma` gives
`inf_{x,y in Gamma} tau_p(x,y) > 0`. The infimum over `I` is then positive, and
Theorem 1.4 with `H = I` gives a unique `I`-infinite cluster, so
`p >= p_u(I;G)`. The first inequality holds by definition. QED.

**(b) If `p_c(G) < p_c(I;G)` for some infinite `I`, then `p_c(G) < p_u(G)`.**
This is immediate from (a). By relative sharpness (Hutchcroft–Pan Theorem 1.8,
any subgroup), the hypothesis is equivalent to `chi^I_p < infinity` for some
`p > p_c(G)`. This extends `fpbs-bs-iff-finite-relative-susceptibility`,
(2 ⇒ 1), to arbitrary infinite subgroups, with no amenability and no
wq-normality.

**(c) Critical finiteness on thin subgroups.** This depends on the critical
two-point bound `tau_(p_c)(u,v) <= gr(G)^(-d(u,v)/2)`, which is still being
checked against its source. If it holds, then every infinite subgroup `I` with
`limsup |S^n ∩ I|^(1/n) < gr(G)^(1/2)` has
`chi^I_(p_c(G)) <= sum_n |S_n ∩ I| gr^(-n/2) < infinity`. In particular this
holds for any subgroup of subexponential ambient growth, such as the cyclic
subgroup of an undistorted element of infinite order.

**(d) The crux.** Call `D(I)` the statement `chi^I_p -> infinity` as
`p ↑ p_c(I;G)`: relative susceptibility diverges at the relative threshold.
Suppose `D(I)` holds and `chi^I_(p_c(G)) < infinity`, and suppose
`p_c(G) = p_c(I;G)`. By left-continuity of `p -> tau_p(o,h)` and monotone
convergence, `chi^I_(p_c(G)) = lim_(p↑p_c) chi^I_p = infinity`, a contradiction.
So `p_c(G) < p_c(I;G)`, and (b) gives the gap.

Classically, `D(Gamma)` is `chi_(p_c) = infinity`, which follows from
Aizenman–Newman's `d chi/dp <= d chi^2`. The relative analogue of that
inequality fails: BK gives `d chi^I/dp <= d sum_u tau_p(o,u) sigma_p(u)`, with
`sigma_p(u) = sum_(h in I) tau_p(u,h)`. That is a quadratic sum over cosets,
the obstruction of Section 4.4 of `relative-susceptibility-reduction.md`, and
not `C (chi^I)^2`.

Two checks are consistent with `D`:
* the `Z`-axis in `Z^2` at `p = 1/2`, where `sum_n n^(-5/24)` diverges;
* a geodesic line in a regular tree, where `p_c(I;G) = 1` and
  `sum_n p^n -> infinity` as `p ↑ 1`.
