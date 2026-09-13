# Free products satisfy the critical L2 boundedness condition

Lane `bs-l2-operator-route`, 2026-09-12. This note does three things:

1. It records, from the TeX sources, what is known about Hutchcroft's condition
   `p_c < p_{2->2}` and which implications are theorems.
2. It tests the universal operator claim
   `fpbs-nonamenability-bounds-critical-connectivity-operator` for
   well-posedness. No counterexample candidate was found.
3. It proves the condition for every Cayley graph of a free product taken with
   the union generating set (Section 3). This is a class for which it was not
   previously known.

Notation. `G=(V,E)` is connected and locally finite.

- `tau_p(u,v) = P_p(u <-> v)`.
- `T_p` is the matrix `(tau_p(u,v))`.
- `p_{q->q} = sup{ p : ||T_p||_{q->q} < infinity }`.
- `chi_p(v) = sum_u tau_p(v,u)`, and `bar chi_p = sup_v chi_p(v)`.
- `A` is the adjacency matrix.

## 1. What is known (read from source)

Sources were downloaded as arXiv e-prints on MSI on 2026-09-12 and read locally:

- arXiv:1804.10191 (Hutchcroft, *Percolation on hyperbolic graphs*, GAFA 2019, `HyperbolicPercolation6.tex`);
- arXiv:1904.05804 (Hutchcroft, *The L2 boundedness condition in nonamenable percolation*, EJP 2022, `ArmExponent8.tex`);
- arXiv:1711.02590 (Hutchcroft, nonunimodular percolation, JAMS 2020);
- arXiv:2002.02916 and arXiv:2207.00701 (Hutchcroft, slightly supercritical percolation I and II);
- arXiv:2409.12283 (Hutchcroft–Pan);
- arXiv:math/0611668 (Kozáková, IJAC 18 (2008) 683–704).

Semantic Scholar lists 12 citing papers for 1904.05804 and 32 for 1804.10191. The titles were scanned. None concerns free products or the L2 condition on infinitely-ended graphs.

### 1.1 The conjecture and its equivalent forms

- **EJP Conjecture 1.3 (L2 boundedness).** Every connected, locally finite,
  nonamenable, quasi-transitive graph has `p_c < p_{2->2}`.
- **GAFA Corollary 2.6.** On every infinite, connected, locally finite graph,
  `||T_p||_{q->q} >= (1-p) / (||A||_{q->q} (p_{q->q} - p))` for `0 < p < p_{q->q}`.
  So `||T_{p_{q->q}}||_{q->q} = infinity`. EJP (2.1) repeats the statement.
  Consequences:
  - `||T_{p_c}||_{2->2} < infinity` if and only if `p_c < p_{2->2}`. So the
    kernel node's "bounded at `p_c`" is exactly Conjecture 1.3. It is well
    posed, and it asks for no uniform constant.
  - With `q = 1`, `chi_{p_c} = infinity`, and `p_{1->1} = p_c` by sharpness of
    the phase transition.
- **GAFA Lemma 2.4.** `T_{p_2} <= sum_k [((p_2-p_1)/(1-p_1)) T_{p_1} A]^k T_{p_1}`
  entrywise, for `p_1 <= p_2`, on any connected locally finite graph. Taking row
  sums gives
  `bar chi_{p_2} <= bar chi_{p_1} / (1 - ((p_2-p_1)/(1-p_1)) deg_max bar chi_{p_1})`
  whenever the denominator is positive. Section 3 uses this form.
- **GAFA Proposition 2.3.** `p_c < p_{2->2}` implies `p_c < p_{q->q}` for every
  `q in (1, infinity)`.
- **GAFA Proposition 2.7 (criterion).** For quasi-transitive `G`,
  `p_c < p_{2->2}` holds if and only if
  `liminf_{p up p_c} ((p_c-p)/(1-p)) bar chi_p sqrt(1 - iota(T_p)^2) < 1/||A||_{2->2}`.
  "In particular, if [this] holds then `p_c(G)<p_u(G)` and `nabla_{p_c}<infinity`."
- **GAFA Lemma 2.8 (Cheeger).**
  `bar chi_p (1 - iota(T_p)) <= ||T_p||_{2->2} <= bar chi_p sqrt(1 - iota(T_p)^2)`.
  Here `iota` is the Cheeger constant of the symmetric substochastic matrix
  `bar chi_p^{-1} T_p`. The proof cites Lyons–Peres Theorem 6.7 and remarks that
  it holds for self-adjoint sub-Markov operators.

### 1.2 Theorems deduced from the condition

These hold for connected, locally finite, nonamenable, quasi-transitive `G`
with `p_c < p_{2->2}`:

- `p_c < p_u` (the stated consequence of GAFA Proposition 2.7). The reason:
  above `p_u`, Harris–FKG gives `tau_p >= theta_p^2 > 0`, so `T_p` is unbounded
  on an infinite graph. Also `p_{2->2} <= p_u`.
- The triangle condition `nabla_{p_c} < infinity`.
- **EJP Theorem 3.1:** `p_{2->2} <= p_exp` on every connected locally finite graph.
- **EJP Theorem 4.1:** `P_{p_c}(rad(K_v) >= n) asymp n^{-1}`.
- **EJP Theorem 5.1:**
  - `||T_{p_c}||_{q->q} asymp q` as `q up infinity`, and `asymp (q-1)^{-1}` as `q down 1`;
  - `p_{q->q} - p_c asymp q^{-1}` as `q up infinity`, and `asymp q-1` as `q down 1`;
  - Corollary 5.2: `E_{p_c}|K_v ∩ W| <= C log |W|`.
- **arXiv:2002.02916 and arXiv:2207.00701:** sharp slightly supercritical
  estimates under `p_c < p_{2->2}`. These include purely exponential cluster
  growth for `p_c < p < p_{2->2}` and anchored expansion of infinite clusters.
- **GAFA closing section:**
  - for `p <= p_{2->2}`, `kappa_p(n)` decays exponentially in `n`, so there is
    no unique infinite cluster at `p_{2->2}`;
  - `E tau_p(X_0, X_n) <= rho^n` along random walk.

### 1.3 Graphs known to satisfy `p_c < p_{2->2}`

The EJP paragraph after Conjecture 1.3 states the known classes; 2002.02916
and 2207.00701 repeat them.

1. **Perturbative classes.** "The proofs that `p_c<p_u` holds under various
   perturbative assumptions such as small spectral radius [Pak–Smirnova-Nagnibeda],
   large Cheeger constant [Schonmann 2001], or high girth [Nachmias–Peres] also
   implicitly yield the stronger claim that `p_c<p_{2->2}` under the same
   assumptions." It follows that every finitely generated nonamenable group has
   **some** Cayley graph with `p_c < p_{2->2}`.
2. **Gromov hyperbolic graphs.** GAFA Theorem 2.1: nonamenable hyperbolic
   quasi-transitive graphs satisfy `p_c < p_{q->q}` for all `q > 1`.
3. **Graphs whose automorphism group has a quasi-transitive nonunimodular
   subgroup.** GAFA Theorem 2.9, via `p_{2->2} >= p_t` from the proof of
   arXiv:1711.02590 Lemma 7.1, and that paper's Theorem 1.11. Example:
   `T_k x H` with `k >= 3`.
4. **Finite products of regular trees** (GAFA closing section, via arXiv:1712.04911).

Stated as not known:

- **EJP:** "groups of cost `>1`, which are known to have `p_c<p_u` ... but are
  not known to have `p_c<p_{2->2}` or to satisfy the triangle condition at
  `p_c`. (As a modest first step in this direction, one could try to prove
  `p_c<p_{2->2}` for infinitely-ended transitive graphs.)"
- **GAFA:** Schonmann (MR1888869) "proved, without verifying the triangle
  condition, that several mean-field exponents hold on every transitive
  nonamenable planar graph and every infinitely ended, unimodular transitive
  graph." The L2 condition is not claimed there.
- **arXiv:2409.12283 (Hutchcroft–Pan):** the companion paper proves
  `p_{2->2} = p_u` for graphs including a tree times a line, "the first examples
  proven to have this property." GAFA ends with the question of when
  `p_u = p_{2->2}`.

### 1.4 Prior work on free products

Kozáková (arXiv:math/0611668, IJAC 2008), Theorems 1–2 and Corollaries 1–2
there. Let `Gamma = G_1 * G_2`, with Cayley graph on `S_1 ∪ S_2`.

- `p_c` is the unique solution of `(chi_1(p)-1)(chi_2(p)-1) = 1`.
- For `p < p_c`, `chi_Gamma = chi_1 chi_2 / (chi_1 + chi_2 - chi_1 chi_2)`.
- `p_c(G_1 * ... * G_n) < min_i p_c(G_i)` unless the product is `C_2 * C_2`.
- `p_exp` of the product is `min_i p_exp(G_i)`.
- `p_u = 1`, since the graph has infinitely many ends.

Kozáková notes that the tree-graded structure is due to Druţu–Sapir. She says
nothing about `T_p` as an operator or about `p_{2->2}`. Section 3 reproves the
connectivity product formula in operator form, because the proof needs it at
the level of matrices, not row sums.
