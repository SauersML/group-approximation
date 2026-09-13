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
   sources do not list this class. Some of its graphs are not hyperbolic, have no
   nonunimodular automorphism subgroup, are not products with trees, and have
   spectral radius above `1/2`.

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
    whenever the denominator is positive. Section 2 does not need this.
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

## 2. The theorem and its proof

**Theorem.** Let `n>=2`, and let `H_1,...,H_n` be nontrivial finitely generated
groups. Let `S_i` be a finite symmetric generating set of `H_i` with `e` not in
`S_i`. Put `Gamma = H_1 * ... * H_n`, `S = S_1 ⊔ ... ⊔ S_n` and
`X = Cay(Gamma,S)`. Exclude the case `n=2`, `|H_1|=|H_2|=2`. Then
`||T_{p_c}||_{2->2} <= lambda < infinity`, with `lambda` given in (2.3). Hence
`p_c(X) < p_{2->2}(X)`, and

    p_{2->2}(X) - p_c(X) >= (1 - p_c(X)) / (|S| lambda).

The excluded graph is the bi-infinite line, where `p_c = p_{2->2} = 1`.

The proof imports two statements of GAFA (arXiv:1804.10191), both quoted in
Section 1.1:

- **(S)** For quasi-transitive `G`, "`||T_p||_{1->1}<infinity` if and only if
  `p<p_c`". This is the sharpness display before Proposition 2.3, and
  `||T_p||_{1->1} = bar chi_p`.
- **(C)** Corollary 2.6 with `q=2`.

Everything else is proved below. The proof does not use amenability or
nonamenability of the factors, unimodularity, or hyperbolicity.

### 2.1 Blocks and the product formula

For `g in Gamma`, the coset `gH_i` spans a copy of `Cay(H_i,S_i)` in `X`. This is
the *block* `gH_i`, of type `i`. Every edge of `X` lies in exactly one block, and
every vertex lies in exactly one block of each type.

Let `Tr` be the bipartite graph on the elements of `Gamma` and the cosets `gH_i`,
with each `g` joined to its `n` cosets.

- `Tr` is connected, because `S` generates `Gamma`.
- `Tr` is a tree. Suppose `g_0, B_1, g_1, ..., B_k, g_k=g_0` is a cycle with
  `k>=2`. Two consecutive blocks share a vertex and are distinct, so they have
  different types. Then `h_j = g_{j-1}^{-1} g_j` lies in `H_{i_j}\{e}` with
  `i_j != i_{j+1}`, and `h_1 ... h_k = e`. This contradicts the normal form theorem.
- Every node has degree at least 2, so `Tr` contains a ray.

For `u != v`, write `u^{-1}v = h_1 ... h_m` in normal form, with
`h_k in H_{i_k}\{e}` and `i_k != i_{k+1}`. Put `g_k = u h_1 ... h_k` and
`B_k = g_{k-1} H_{i_k}`. Then `u=g_0, B_1, g_1, ..., B_m, g_m=v` is the geodesic
from `u` to `v` in `Tr`. For `h in H_i\{e}`, let `a_{i,p}(h)` be the probability
that `e` and `h` are connected in percolation on `Cay(H_i,S_i)`.

**Lemma 2.1 (product formula).** `tau_p(u,v) = prod_{k=1}^m a_{i_k,p}(h_k)`.

*Proof.* A path in `X` gives a walk in `Tr`: an edge `xx'` of type `i` becomes
`x, xH_i, x'`. The element nodes of the walk are the vertices of the path. A walk
in a tree passes through every node of the geodesic between its endpoints. So
every path from `u` to `v` visits `g_1, ..., g_{m-1}`. The first visits come in
this order, because `g_k` lies on the geodesic from `u` to `g_{k+1}`.

Let `gamma` be a self-avoiding open path from `u` to `v`. Let `gamma_k` be its
segment from the first visit of `g_{k-1}` to the first visit of `g_k`. Suppose
`gamma_k` leaves `B_k`, and let `xx'` be its first edge outside `B_k`, lying in a
block `B' != B_k`.

- Then `x in B_k`, and `x != g_k`.
- In `Tr`, removing `x` separates `B'` from `B_k`, and so from `g_k`.
- So the walk of `gamma_k` visits `x` again before reaching `g_k`. This contradicts
  self-avoidance.

So `gamma_k` uses only edges of `B_k`, and

    {u <-> v} = E_1 ∩ ... ∩ E_m,   E_k = {g_{k-1} <-> g_k through open edges of B_k}.

The reverse inclusion is concatenation. Distinct blocks share no edge, so the
`E_k` are independent. Left multiplication by `g_{k-1}^{-1}` carries `B_k` onto
`Cay(H_{i_k},S_{i_k})` and `g_k` to `h_k`. So `P_p(E_k) = a_{i_k,p}(h_k)`. ∎

**Masses and the type matrix.** Let `m_i(p) = sum_{h in H_i\{e}} a_{i,p}(h)`.
This is the expected cluster size of `e` in `Cay(H_i,S_i)`, minus one. Since
`a_{i,p}(s) >= p` for `s in S_i`, `m_i(p)` lies in `[p, infinity]`. Let `Q(p)` be
the `n x n` matrix with `Q_{ij} = m_i [i != j]`, and let `m = (m_1,...,m_n)^T`.
Summing Lemma 2.1 over normal forms gives

    (2.1)  chi_p = 1 + sum_{l>=1} sum_{i_1,...,i_l} m_{i_1} ... m_{i_l}
                 = 1 + sum_{l>=1} 1^T Q^{l-1} m.

The inner sum runs over sequences whose consecutive indices differ. The second
form holds whenever every `m_i` is finite. For `n=2`, (2.1) is Kozáková's
Theorem 2, `chi_1 chi_2 / (chi_1 + chi_2 - chi_1 chi_2)` with `chi_i = 1 + m_i`.

### 2.2 The critical point

Write `p_c = p_c(X)`. `X` is `|S|`-regular, so `chi_p <= sum_k (|S|p)^k`. By (S),
`p_c >= 1/|S| > 0`.

**Lemma 2.2.** `p_c < 1`. Every `m_i(p_c)` is at most `1/p_c`, and the spectral
radius satisfies `rho(Q(p_c)) <= 1`.

*Proof.* Matrix norms are `||.|| = ||.||_{infinity->infinity}`, the maximum row
sum. The proof uses four standard facts about finite matrices:

- Gelfand's formula `rho(Q) = lim_l ||Q^l||^{1/l}`;
- the bound `rho(Q)^l <= ||Q^l||`;
- monotonicity of `rho` in the entries of a nonnegative matrix;
- continuity of `rho` in the entries.

1. *Below `p_c`.* Let `0<p<p_c`.
   - By (S), `chi_p < infinity`. So every `m_i(p)` is finite and
     `1^T Q^l m -> 0`.
   - Since `m >= p 1`, `||Q^l|| <= p^{-1} 1^T Q^l m -> 0`, so `rho(Q(p)) < 1`.
   - Also `(Q^2)_{ii} = m_i sum_{j != i} m_j >= p m_i`, and
     `(Q^{2k})_{ii} >= ((Q^2)_{ii})^k`. So `p m_i(p) <= rho(Q(p))^2 < 1`.
2. *Left continuity.* `a_{i,p}(h)` is the increasing limit, as `R` grows, of the
   probability that `e` and `h` are connected inside the ball of radius `R`. Each
   of these is a polynomial in `p`.
   - So `m_i` is a supremum of continuous nondecreasing functions. It is lower
     semicontinuous and nondecreasing, hence left continuous.
   - By step 1, `m_i(p_c) = lim_{p up p_c} m_i(p) <= 1/p_c`.
   - So `Q(p) -> Q(p_c)` entrywise with finite limits, and `rho(Q(p_c)) <= 1` by
     continuity.
3. *`p_c < 1`.* As `p up 1`, `a_{i,p}(h) >= p^{|h|} -> 1`, so
   `liminf m_i(p) >= |H_i| - 1`.
   - If `n>=3`, then `Q(p) >= c(p)(J-I)` entrywise, where `c(p) = min_i m_i(p)`.
     Since `rho(J-I) = n-1 >= 2`, `rho(Q(p)) >= 2c(p)`, and `liminf c(p) >= 1`.
   - If `n=2`, then `rho(Q(p)) = (m_1 m_2)^{1/2}`, and
     `liminf m_1 m_2 >= (|H_1|-1)(|H_2|-1) >= 2`.

   So some `p<1` has either an infinite `m_i(p)`, or `rho(Q(p)) > 1`. In the
   second case `1^T Q^l m >= p ||Q^l|| >= p rho(Q(p))^l`. Either way
   `chi_p = infinity` by (2.1), so `p_c <= p < 1` by (S). ∎

Kozáková's Theorem 1 gives equality, `m_1 m_2 = 1` at `p_c`, for `n=2`. The proof
needs only the inequality.

### 2.3 The Schur test

**Lemma 2.3.** Let `K >= 0` be a symmetric matrix indexed by a countable set `V`.
Suppose `phi: V -> (0,infinity)` and `lambda < infinity` satisfy
`sum_y K(x,y) phi(y) <= lambda phi(x)` for every `x`. Then
`||K||_{2->2} <= lambda`.

*Proof.* Let `f,g in l^2(V)`. By Cauchy–Schwarz, `sum_{x,y} K(x,y)|f(x)||g(y)|` is
at most the product of

    ( sum_{x,y} K(x,y) |f(x)|^2 phi(y)/phi(x) )^{1/2}
    ( sum_{x,y} K(x,y) |g(y)|^2 phi(x)/phi(y) )^{1/2}.

In the first factor sum over `y` first. In the second sum over `x` first, using
`K(x,y) = K(y,x)`. The product is then at most `lambda ||f|| ||g||`. ∎

With `phi = 1`, the lemma gives `||T_p||_{2->2} <= bar chi_p`, so
`p_c <= p_{2->2}`.

### 2.4 The weight

Fix a ray `r_0, r_1, ...` in `Tr`. Its Busemann function is
`b(x) = lim_k (d(x,r_k) - k)`, and the limit exists because the sequence is
eventually constant.

- Every node `x` has exactly one neighbour with `b` smaller by one: the next node
  on the geodesic from `x` toward the ray. This is the *parent* of `x`. Every
  other neighbour has `b` larger by one.
- Along a geodesic of `Tr`, the increments of `b` are a run of `-1`s followed by
  a run of `+1`s. A `+1` followed by a `-1` would return to the previous node.

So a vertex `g` of `X` has a *parent block*, and its other `n-1` blocks are its
*child blocks*. A block `B` has a *parent vertex*, and its other vertices are its
*child vertices*. A vertex is a child vertex of its parent block and the parent
vertex of each of its child blocks.

For `theta in (0,1)`, put `phi(g) = theta^{b(g)/2}`. Along the geodesic
`g_0, B_1, g_1, ..., B_m, g_m` from `u` to `v`, step `k` is one of three kinds:

- *up*, `b(g_k) = b(g_{k-1}) - 2`: `B_k` is the parent block of `g_{k-1}`, and
  `g_k` is the parent vertex of `B_k`;
- *across*, `b(g_k) = b(g_{k-1})`: `B_k` is the parent block of `g_{k-1}`, and
  `g_k` is a child vertex of `B_k`;
- *down*, `b(g_k) = b(g_{k-1}) + 2`: `B_k` is a child block of `g_{k-1}`, and
  `g_k` is a child vertex of `B_k`.

The fourth combination would be a `+1` followed by a `-1`. By the run structure,
the steps read `up^j across^eps down^l` with `eps in {0,1}`. Then
`phi(v)/phi(u) = theta^{l-j}`.

### 2.5 The bound at `p_c`

Put `M = max_i m_i(p_c)` and `rho = rho(Q(p_c))`. By Lemma 2.2, `M <= 1/p_c` and
`rho <= 1`. Put

    alpha = max_i sup_{h in H_i\{e}} a_{i,p_c}(h) <= 1 - (1-p_c)^{max_i |S_i|} < 1.

The bound holds because a connection from `e` to `h != e` needs an open edge at
`e`, and it is below 1 because `p_c < 1`. Fix `theta in (alpha,1)`. Then
`theta rho < 1`, so Gelfand's formula makes
`C_theta = sum_{l>=0} theta^l ||Q(p_c)^l||` finite.

Fix `u`. Use Lemma 2.1 to sum `tau_{p_c}(u,v)` over the `v` whose geodesic has the
pattern `up^j across^eps down^l`:

- The `j` up steps are forced, and each contributes a factor at most `alpha`.
- An across step runs over the child vertices of one block of some type `i`. It
  contributes at most `m_i <= M`.
- The down steps choose a child block of type `i_1`, then a child vertex of it,
  then a child block of type `i_2 != i_1`, and so on. Sum over the last choice
  first. The down steps then contribute at most
  `sum_{i_1,...,i_l} m_{i_1} ... m_{i_l} = 1^T Q^{l-1} m <= nM ||Q^{l-1}||`, with
  consecutive indices differing.

Multiply by `phi(v)/phi(u) = theta^{l-j}` and sum over all patterns:

    (2.2)  (T_{p_c} phi)(u) <= lambda phi(u),
    (2.3)  lambda = (1+M)(1 + nM theta C_theta) / (1 - alpha/theta).

Every `v` has exactly one pattern. The bound also counts choices that are not
geodesics, such as a down step back into the block just left, and these only
enlarge it. By Lemma 2.3, `||T_{p_c}||_{2->2} <= lambda`.

*Proof of the Theorem.* Lemma 2.3 gives `p_c <= p_{2->2}`. If
`p_c = p_{2->2}`, then (C) gives `||T_{p_c}||_{2->2} = infinity`, which
contradicts (2.2). So `p_c < p_{2->2}`. At `p = p_c`, (C) reads
`lambda >= (1-p_c) / (||A||_{2->2} (p_{2->2} - p_c))`, and
`||A||_{2->2} <= |S|`. ∎

### 2.6 What the proof uses

1. A tree of cut vertices and blocks. This gives the product formula.
2. A uniform bound `alpha < 1` on connection probabilities inside a block.
3. A finite matrix that bounds the sums along down paths, with spectral radius at
   most 1 at `p_c`. This is the only place where criticality enters.

The weight is what separates the two norms. From each vertex there is exactly one
up path, and its weight decays like `alpha^j`. The mass that makes `chi_{p_c}`
infinite lies on down paths, and `theta^l` damps it. The weight `phi` is
unbounded, which the Schur test allows. Section 4 records where each item fails
beyond free products.

## 3. Novelty

**What the sources already give.**

- *Groups.* EJP deduces from Pak and Smirnova-Nagnibeda that every finitely
  generated nonamenable group has *some* Cayley graph with `p_c<p_{2->2}`
  (Section 1.3). So the Theorem gives no group its first such Cayley graph. What
  is new concerns specific graphs: every union generating set works, and the gap
  is explicit.
- *Some graphs of the class.* `Cay(Z * Z/2, {t, t^{-1}, a})` is the 3-regular tree.
  Its blocks are lines and single edges, and by Proposition 3.1 below every cycle
  lies in one block. The tree is hyperbolic, and its automorphism group has a
  quasi-transitive nonunimodular subgroup. More generally, if every `H_i` is
  hyperbolic then `Gamma` is hyperbolic, and GAFA already covers `X`. I did not
  determine which other graphs of the class fall under GAFA Theorem 2.9.

**The example.** Let `H = H_3(Z)` be the integer Heisenberg group, and let
`K = Z/2 = {e,a}`.

- **A generating set with no extra symmetry.** Leemann–de la Salle, *Cayley graphs
  with few automorphisms: the case of infinite groups* (arXiv:2010.06020),
  Theorem `thm:main`: "Every finitely generated group `G` that is not virtually
  abelian admits a finite degree Cayley graph whose automorphism group is not
  larger than `G` acting by left-translation."
  - Their Cayley graphs are simple and unoriented, on a symmetric generating set
    `S ⊆ G\{1}`.
  - `H` is not virtually abelian. So `H` has a finite symmetric generating set
    `S_H`, with `e` not in `S_H`, such that `Aut(Cay(H,S_H)) = H`.
  - The earlier paper arXiv:1812.02199, Theorem `thm:mainUndirected`, also gives
    this. It needs `G` to be non-abelian, not generalized dicyclic, and to have an
    element of large order. A generalized dicyclic group contains an element of
    order 4, and `H` is torsion free.
- Put `Gamma = H * K`, `S = S_H ⊔ {a}` and `X = Cay(Gamma,S)`. The Theorem gives
  `p_c(X) < p_{2->2}(X)`.

**Proposition 3.1.** Every simple cycle of `X` uses edges of only one block, and
`Aut(X) = Gamma` acting by left multiplication.

*Proof.*

1. *Cycles.* Suppose a simple cycle uses edges of two blocks. Then at some vertex
   `x` it passes from an edge `yx` of a block `B` to an edge `xy'` of a block
   `B' != B`.
   - In `Tr`, removing `x` separates `B` from `B'`. Then `y` lies in the component
     of `B`, and `y'` lies in the component of `B'`.
   - The rest of the cycle is a path from `y'` to `y` that avoids `x`. Its walk in
     `Tr` avoids `x`, which is a contradiction.

   This holds for every free product in Section 2.
2. *No cut vertex inside a block.* `H` is one-ended. It is amenable, so it does not
   have infinitely many ends, and it is not virtually `Z`. A one-ended
   vertex-transitive graph `Y` has no cut vertex:
   - Suppose it has one. For a cut vertex `v`, the graph `Y - v` has at least two
     components, and only one of them is infinite.
   - Choose a cut vertex `v` and a finite component `C` of `Y - v` with `|C|`
     minimal, and let `w in C`. By transitivity `w` is a cut vertex.
   - Let `C'` be a finite component of `Y - w`. It contains a neighbour of `w`, so
     `C' ∪ {w}` is connected. It also avoids `v`: the infinite component of
     `Y - v`, together with `v`, is connected and avoids `w`, so it lies in the
     infinite component of `Y - w`.
   - So `C' ∪ {w} ⊆ C`, and `|C'| < |C|`. This contradicts minimality.

   `Cay(H,S_H)` is connected, has at least 3 vertices and no cut vertex, so it has
   no bridge. A bridge would have an endpoint of degree at least 2, and that
   endpoint would be a cut vertex.
3. *Automorphisms.* By steps 1 and 2, the edges of `X` that lie on no cycle are
   exactly the `a`-edges.
   - So every automorphism `phi` maps `a`-edges to `a`-edges. Removing the
     `a`-edges leaves the cosets `gH` as the components, so `phi` permutes the
     cosets.
   - The edges of `X` inside `gH` are the `S_H`-edges, since `a` is not in `H`. If
     `phi(gH) = g'H`, then `x -> g'^{-1} phi(g x)` is an automorphism of
     `Cay(H,S_H)`.
   - So it is left multiplication by some `h_0 in H`, and `phi(y) = g' h_0 g^{-1} y`
     for `y in gH`. Hence `phi(ys) = phi(y)s` for `s in S_H`.
   - Also `phi(ya) = phi(y)a`, because every vertex has exactly one `a`-edge.
   - By induction on word length, `phi(y) = phi(e) y` for every `y`. ∎

**Proposition 3.2.** `X` has none of the non-perturbative properties of Section
1.3, and its spectral radius is at least `4/5`.

- *Not hyperbolic.* `H` contains `Z^2`, generated by a non-central generator and
  the centre. A hyperbolic group has no subgroup isomorphic to `Z^2`. So `Gamma`
  is not hyperbolic, and neither is any of its Cayley graphs.
- *No nonunimodular subgroup.* By Proposition 3.1, every subgroup of `Aut(X)` acts
  freely on the vertices. Its stabilizers are trivial, so it is unimodular, and
  GAFA Theorem 2.9 does not apply.
- *Not a product with a tree.* A Cartesian product of two connected graphs, each
  with at least two vertices, has no cut vertex. Every vertex `g` of `X` is a cut
  vertex, because in `Tr` the node `g` separates `ga` from `gH\{g}`.
- *Spectral radius.* Let `d = |S_H| + 1` be the degree.
  - Simple random walk on `X` returns to `e` at time `2k` with probability at
    least `((d-1)/d)^{2k} p^H_{2k}(e,e)`. That is the probability of taking only
    `S_H`-steps and returning, where `p^H` is simple random walk on `Cay(H,S_H)`.
  - `H` is amenable, so `p^H_{2k}(e,e)^{1/2k} -> 1` by Kesten's theorem. So
    `rho(X) >= (d-1)/d`.
  - `H` is torsion free and not cyclic, so `|S_H| >= 4`, and `rho(X) >= 4/5`.

  The abstract of arXiv:2002.02916 names the class `rho<1/2`.
- *Cheeger constant and girth.* Let `F ⊆ H` be finite. Every vertex of `F` has its
  `a`-edge leaving `F`.
  - Since `H` is amenable, the edge Cheeger constant satisfies `h(X) <= 1`, against
    degree `d >= 5`.
  - Take non-commuting `s,t in S_H`. The word `s t s^{-1} t^{-1} s^{-1} t s t^{-1}`
    is a conjugate of `[s,[s,t]]`, which is trivial because `[s,t]` is central.
  - Its letters are four distinct elements, and no two consecutive letters are
    inverse, even cyclically. So it traces a closed non-backtracking walk of
    length 8, and `X` has girth at most 8.

  The perturbative papers ([MR1833805] on large Cheeger constant, [MR3005730] on
  high girth) were not re-read. Their thresholds are not quoted here, and this
  note does not claim that `X` lies outside those two classes.

**What is new, relative to the verified sources.** The Theorem covers graphs such
as `X`:

- not hyperbolic;
- with no quasi-transitive nonunimodular automorphism subgroup;
- not products with trees;
- with spectral radius above `1/2`.

No source read for this note gives `p_c<p_{2->2}` for such graphs. The EJP remark
proposes infinitely-ended transitive graphs as "a modest first step". The Theorem
settles the special case of free-product Cayley graphs on union generating sets,
not that question.
