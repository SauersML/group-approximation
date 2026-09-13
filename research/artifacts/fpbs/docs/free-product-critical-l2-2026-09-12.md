# Free products satisfy the critical L2 boundedness condition

Lane `bs-l2-operator-route`, 2026-09-12. This note does three things:

1. It records what is known about Hutchcroft's condition `p_c < p_{2->2}`,
   and which implications are theorems. Everything in Section 1 was read from
   the TeX sources.
2. It tests the universal operator claim
   `fpbs-nonamenability-bounds-critical-connectivity-operator` for being well
   posed (Section 1.1). No counterexample candidate was found.
3. It proves the condition for every Cayley graph of a free product on the
   union generating set (Section 2). Section 3 treats novelty: the verified
   sources do not list this class, and some of its graphs lie outside every
   listed class.

Notation. `G=(V,E)` is connected and locally finite.

- `tau_p(u,v) = P_p(u <-> v)`, and `T_p` is the matrix `(tau_p(u,v))`.
- `p_{q->q} = sup{ p : ||T_p||_{q->q} < infinity }`.
- `chi_p(v) = sum_u tau_p(v,u)`, and `bar chi_p = sup_v chi_p(v)`.
- `A` is the adjacency matrix.

## 1. What is known (read from source)

Sources were downloaded as arXiv e-prints on MSI on 2026-09-12 and read locally:

- arXiv:1804.10191, Hutchcroft, *Percolation on hyperbolic graphs* (GAFA 2019);
- arXiv:1904.05804, Hutchcroft, *The L2 boundedness condition in nonamenable percolation* (EJP 2022);
- arXiv:1711.02590, Hutchcroft, *Nonuniqueness and mean-field criticality for
  percolation on nonunimodular transitive graphs* (JAMS 2020);
- arXiv:2002.02916 and arXiv:2207.00701, Hutchcroft, *Slightly supercritical
  percolation on nonamenable graphs* I and II;
- arXiv:2409.12283, Hutchcroft–Pan, *Percolation at the uniqueness threshold via
  subgroup relativization*;
- arXiv:math/0611668, Kozáková, *Percolation and ... free products* (IJAC 18 (2008) 683–704).

**Numbering.**

- GAFA Section 2 was numbered by counting its theorem environments, which share
  one per-section counter. EJP itself cites the lower bound as "[Corollary 2.6]"
  of 1804.10191, which confirms the count.
- EJP results are named by their TeX labels.
- Kozáková's results use one global counter, and they are numbered by counting.

**Citing papers.** Semantic Scholar lists 32 papers citing 1804.10191 and 12
citing 1904.05804. The titles were scanned, not the texts. None is about free
products or about the L2 condition on infinitely-ended graphs.

### 1.1 The conjecture and its equivalent forms

- **EJP `conj:pcp22` (Conjecture 1.3).** "Let `G` be a connected, locally finite,
  nonamenable, quasi-transitive graph. Then `p_c(G)<p_{2->2}(G)`."
- **Sharpness (EJP).** `p_c(G)=p_{1->1}(G)=p_{infinity->infinity}(G)` for every
  quasi-transitive `G`.
- **GAFA Lemma 2.4.** For connected locally finite `G` and `0<=p_1<=p_2<=1`,
  `T_{p_1} <= T_{p_2} <= sum_{k>=0} [((p_2-p_1)/(1-p_1)) T_{p_1} A]^k T_{p_1}`
  entrywise.
  - The row sums of `T_{p_1} A` are at most `deg_max * bar chi_{p_1}`.
  - So `bar chi_{p_2} <= bar chi_{p_1} / (1 - ((p_2-p_1)/(1-p_1)) deg_max bar chi_{p_1})`
    whenever the denominator is positive. Section 2 uses this form.
- **GAFA Corollary 2.6.** "Let `G` be an infinite, connected, locally finite graph.
  Then `||T_p||_{q->q} >= (1-p)/(||A||_{q->q}(p_{q->q}-p))` for every
  `0<=p<p_{q->q}`. In particular, `||T_{p_{q->q}}||_{q->q}=infinity`."
  - EJP repeats this as `eq:general_norm_lower_bound`.
  - EJP adds: "It is shown in [1804.10191] that [the conjecture] is implied by the
    weaker statement that `||T_{p_c}||_{2->2}<infinity`."
  - **Consequence for the kernel node.** "`T_{p_c}` is bounded on `l^2`" is
    equivalent to `p_c < p_{2->2}`. So the universal operator claim is exactly
    Conjecture 1.3. It is well posed, and it needs no uniform constant.
- **GAFA Proposition 2.3.** "Let `G` be a connected, locally finite,
  quasi-transitive graph. If `p_c(G) < p_{2->2}(G)` then `p_c(G) <p_{q->q}(G)`
  for every `q in (1,infinity)`."
- **GAFA Proposition 2.7.** "Let `G` be a connected, locally finite,
  quasi-transitive graph. Then `p_c(G)<p_{2->2}(G)` if and only if
  `liminf_{p up p_c} ((p_c-p)/(1-p)) bar chi_p sqrt(1-iota(T_p)^2) < 1/||A||_{2->2}`.
  In particular, if [this] holds then `p_c(G)<p_u(G)` and `nabla_{p_c}<infinity`."
  Here `iota(T_p) = 1 - sup_K sum_{u,v in K} tau_p(u,v) / (bar chi_p |K|)`, with
  `K` ranging over finite sets.
- **GAFA Lemma 2.8.** For connected locally finite `G` and `0<p<p_{1->1}(G)`:
  `bar chi_p (1-iota(T_p)) <= ||T_p||_{2->2} <= bar chi_p sqrt(1-iota(T_p)^2)`.
  The proof cites [LP, Theorem 6.7]. It adds that Cheeger's inequality "is
  usually stated for self-adjoint Markov operators but the proof is valid for
  self-adjoint sub-Markov operators, or, equivalently, symmetric substochastic
  matrices."

### 1.2 Theorems deduced from the condition

- **Uniqueness and the triangle condition (EJP, after Conjecture 1.3).** The
  condition implies `p_c<p_u`: "if `p>p_u` then
  `inf_{u,v} T_p(u,v) >= inf_{u,v} P_p(u -> infinity) P_p(v -> infinity) >0` by
  the Harris-FKG inequality, so that `||T_p||_{2->2}=infinity`."
  It also implies the triangle condition, since
  "`nabla_p(v)=T_p^3(v,v) <= ||T_p||_{2->2}^3`".
- **EJP `thm:p2to2pexp`.** "Let `G` be a connected, locally finite graph. Then
  `p_{2->2}(G)<=p_exp(G)`."
- **EJP, results under the hypothesis.** The next three assume `G` is connected,
  locally finite, nonamenable, quasi-transitive, with `p_c<p_{2->2}`:
  - `thm:ext_radius`: `P_{p_c}(rad(K_v) >= n) asymp n^{-1}`.
  - `thm:qtoq_exponents`:
    - `||T_{p_c}||_{q->q} asymp q` as `q up infinity`, and `asymp (q-1)^{-1}` as `q down 1`;
    - `p_{q->q}-p_c asymp q^{-1}` as `q up infinity`, and `asymp q-1` as `q down 1`.
  - `cor:logbound`: `E_{p_c}|K_v ∩ W| <= C log|W|` for all `W` with `|W|>=2`.
- **arXiv:2002.02916 (abstract).** Assume `G` is transitive, nonamenable, with
  `p_c<p_{2->2}`. Then for `|p-p_c|<delta`:
  - `P_p(n<=|K|<infinity) asymp n^{-1/2} exp[-Theta(|p-p_c|^2 n)]`;
  - `P_p(r<=Rad(K)<infinity) asymp r^{-1} exp[-Theta(|p-p_c| r)]`;
  - `gamma'=1` and `Delta'=2`.

  "These results apply in particular to Cayley graphs of nonelementary hyperbolic
  groups, to products with trees, and to transitive graphs of spectral radius
  `rho<1/2`."
- **arXiv:2207.00701 (abstract).** Under the L2 boundedness condition, "the
  volume growth of infinite clusters is always purely exponential ... in the
  regime `p_c<p<p_{2->2}`". The paper also gives precise intrinsic ball
  estimates for `p_c<p<=p_c+delta`, and bounds on the anchored Cheeger constant.
- **GAFA `prop:p2to2kappa`.** For quasi-transitive `G` and `q in [2,infinity]`:
  `kappa_p(n) := inf{tau_p(u,v): d(u,v)<=n} <= gr(G)^{-(q-1)n/q}` for
  `0<=p<=p_{q->q}(G)`. GAFA concludes that "there cannot be a unique infinite
  cluster at `p_{2->2}` on any quasi-transitive nonamenable graph."
- **GAFA `prop:nonuniquenessatpell2`.** For `G` transitive and nonamenable, with
  spectral radius `rho(G)`: `E[tau_p(X_0,X_n)] <= rho(G)^n` for `0<=p<=p_{2->2}`.

### 1.3 Graphs known to satisfy `p_c < p_{2->2}`

**EJP, after Conjecture 1.3:**

- Perturbative classes: "the proofs that `p_c<p_u` holds under various
  perturbative assumptions such as small spectral radius [MR1756965], large
  Cheeger constant [MR1833805], or high girth [MR3005730] also implicitly yield
  the stronger claim that `p_c<p_{2->2}` under the same assumptions. In
  particular, it can be deduced from the work of Pak and Smirnova-Nagnibeda
  [MR1756965] that every finitely generated nonamenable group has a Cayley graph
  for which `p_c<p_{2->2}`."
- Non-perturbative classes: the conjecture "holds under the additional assumption
  that `G` is either Gromov hyperbolic [1804.10191] or has a quasi-transitive
  nonunimodular subgroup of automorphisms [1711.02590]. The latter condition
  holds, for example, if `G=T_k x H` is the Cartesian product of a regular tree
  of degree `k>=3` with a quasi-transitive graph `H`."

**GAFA Theorem 2.9.** "Let `G` be a connected, locally finite graph, and suppose
that `Aut(G)` has a quasi-transitive nonunimodular subgroup. Then
`p_c(G)< p_{q->q}(G)` for every `q in (1,infinity)`." The proof shows
`p_{2->2} >= p_t(G,Gamma)` "from the proof of [1711.02590, Lemma 7.1]", then
applies [1711.02590, Theorem 1.11].

**GAFA closing section.** "It can be deduced from the methods of [1712.04911]"
that `p_{q->q}` is continuous and strictly increasing on `[1,2]` "for the product
of finitely many trees each of which is regular of some degree `>=3`." These
graphs already fall under Theorem 2.9.

**Not known, per the sources:**

- EJP: "A notable exception is given by groups of cost `>1`, which are known to
  have `p_c<p_u` [Gaboriau, Lyons] but are not known to have `p_c<p_{2->2}` or to
  satisfy the triangle condition at `p_c`. (As a modest first step in this
  direction, one could try to prove `p_c<p_{2->2}` for infinitely-ended
  transitive graphs.)"
- GAFA: "The proofs of [Lalley; Benjamini–Schramm; Gaboriau; Lyons] establish
  `p_c<p_u` without establishing `p_c<p_{2->2}`."
- GAFA: Schonmann [MR1888869] "proved, without verifying the triangle condition,
  that several mean-field exponents hold on every transitive nonamenable planar
  graph and every infinitely ended, unimodular transitive graph."
- arXiv:2409.12283: the companion paper proves that certain graphs, "including
  the product of a tree and a line", have `p_{2->2}=p_u`. "These are the first
  examples proven to have this property."
- GAFA Question: "Under what conditions is `p_u(G)=p_{2->2}(G)`?"

### 1.4 Prior work on free products

Kozáková (arXiv:math/0611668), for the Cayley graph of `G_1 * G_2` on
`S_1 ∪ S_2`:

- **Theorem 1.** `0<p_c<=1` "is the unique solution" of
  `(chi_1(p)-1)(chi_2(p)-1)=1`.
- **Theorem 2.** `E_p|C| = chi_1 chi_2 / (chi_1+chi_2-chi_1 chi_2)` for `p<p_c`.
- **Corollaries 3–4.** The same for `n` factors.
- **Proposition 6.** `p_exp(G_1*...*G_n)=min_i p_exp(G_i)`.
- **Corollary 7.** If the product is not virtually `Z`, then
  `p_c(G_1*...*G_n) < min_i p_c(G_i) <= ... = p_exp(G_1*...*G_n) <= p_u = 1`.

Kozáková also records:

- `p_c=1` if and only if `|G_1|=|G_2|=2`.
- The Cayley graph has a tree-graded structure (Druţu–Sapir): "different `M_j`
  and `M_k` intersect by at most one point, and every simple loop in the Cayley
  graph is in one of the `M_i`."
- "The results of this paper can be generalized to arbitrary transitive locally
  finite tree-graded graphs."
- A nontrivial free product other than `C_2*C_2` has infinitely many ends, so
  `p_u=1`.

Nothing in the paper concerns `T_p` as an operator or `p_{2->2}`. Section 2
reproves the connectivity product formula in matrix form, which the proof needs.
