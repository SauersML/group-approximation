---
rg: 2
id: fpbs-walk-rate-holes-fail-on-unimodular-random-graphs
kind: claim
title: On the Angel--Hutchcroft nonamenable unimodular random graph the annealed walk connectivity rate jumps from at most rho to one at p_c, so the walk-rate holes are false for every argument that uses only product-measure, mass-transport and expansion inputs
distinct_from:
  fpbs-unimodular-critical-quotients-can-have-zero-pu: that contracts critical clusters into a quotient multigraph and refutes generic quotient properties; this keeps the Angel--Hutchcroft graph itself, proves the annealed Schramm lemma, a uniform spectral gap and the uniqueness lower bound there, and refutes the walk-rate holes (IS, green-visit, uniform pivotal budget, cheap certificates) in their root-averaged form
  fpbs-soft-collapse-iff-invariant-sparse-spines: that keeps the Cayley graph and drops product structure above p_c; this keeps exact Bernoulli product structure at every parameter and drops transitivity, so the two obstructions are orthogonal
  fpbs-finite-energy-fkg-collapse-over-central-z2-slabs: same orthogonality; that family is not a product measure above p_c, while here the percolation is exactly Bernoulli at every p
---

OPEN. A proof attempt is in
`fpbs-walk-rate-holes-fail-on-unimodular-random-graphs-proof`. Referees accepted
Theorems 1 and 2 and the annealed Corollary. They did not accept the class-kill:
see ## Attempts.

**Setting.** `(H,o)` is a unimodular random rooted graph with root law `mu`.
Its degrees are at most a deterministic `D`, and every realization has edge
expansion `Phi = inf |d_E K| / vol(K) >= Phi_0 > 0`. `P` is the lazy simple
random walk, `rho_bar = (1 + sqrt(1 - Phi_0^2))/2 < 1`, and `mu_hat` is the
degree-biased root law. Percolation is Bernoulli bond percolation on each
realization. The annealed walk connection probability and rate are

    a_n(p) = E_mu_hat P_p(o <-> X_n),   lambda_hat(p) = limsup_n a_n(p)^(1/n).

**Theorem 1 (package valid on every such graph).**

1. (Spectral gap) Every realization has `||P||_(l2(deg))<=rho_bar`.
2. (Annealed Schramm lemma) If `p <= p_c(H)` a.s., then `a_n(p) <= rho_bar^n`
   for all `n`. Critical finiteness is not used.
3. (Uniqueness floor) If for `p` there is a.s. exactly one infinite cluster, then
   `a_n(p) >= (E_mu_hat theta_p)^2 > 0` for all `n`.
4. (Annealed strong converse) For `c=p_c`, `q>c`, `b < -log(rho_bar)/k(q,c)`
   there is `eta>0` such that `E_mu_hat P_q(certificate of o<->X_n by floor(bn)
   queries) <= e^(-eta n)`.

**Theorem 2 (the Angel--Hutchcroft graph).** Take `H = H~(M)` from Angel--Hutchcroft
(arXiv:1710.03003, Proposition 4.2) with `M` large and `q` as there. Then
`Phi_0 >= 1/(D M (D+1))`, `p_c = p_u = q`, and for every `p>q` there is a
unique infinite cluster. Hence

    lambda_hat(q) <= rho_bar < 1,   lambda_hat(p) = 1 for every p > q,
    E_mu_hat A(q) <= 1/(1-rho_bar),  E_mu_hat A(p) = infinity for p > q,

where `A = sum_n P(o<->X_n)` is the expected number of walk visits to the
cluster.

**Corollary (what is false on H~).** The following fail on `H~` in annealed form:

* the right-continuity (IS) of the walk rate at `p_c`
  (`fpbs-integrated-sensitivity-universal`);
* the green-visit criterion, finiteness of `A(p)` for some `p>p_c`;
* the pivotal budget `E_p[N | o<->X_n in B_R] <= Cn` on `[p_c,p0]` with
  constants `C, p0` that do not depend on the root
  (`fpbs-pivotal-budget-universal`);
* the Section 5 construction of `research/artifacts/fpbs/query-strong-converse.md`.
  On `H~` uniqueness holds at every `q>p_c` and exhaustive search finds a path,
  yet cheap certificates are exponentially rare. So "uniqueness produces cheap
  certificates" is false without a further input.

**Class killed.** Let `K` be the class of arguments whose inputs are only:

1. quenched facts about exact Bernoulli product measure on a fixed bounded-degree
   graph, at every parameter: Harris--FKG, BK/Reimer, Russo--Margulis, the
   Aizenman--Barsky and Menshikov differential inequalities, sprinkling and
   independent increments, insertion and deletion tolerance, and finite-volume
   Russo integration;
2. the mass-transport principle, and reversibility and stationarity of the
   environment seen from the walker;
3. a uniform positive edge expansion (hence `rho<1`), and bounded degree;
4. no infinite cluster for `p<p_c`, uniqueness for `p>p_u`, and the Lyons--Schramm
   and Aldous--Lyons indistinguishability and `0/1/infinity` theorems;
5. everything derived from 1--4, including Theorem 1 above.

An argument in `K` whose conclusion, for a Cayley graph, is one of the holes in the
Corollary would, run with root averages, prove the same statement on `H~`. That is
false by Theorem 2.

**Where every member dies.** At the continuation `p_c -> p_c + eps` of the walk
rate. All of Theorem 1 holds on both sides of it; the jump happens at it. The
invariant `H~` exhibits: an invariant subgraph whose components are invariantly
amenable (the type-1 copies of the canopy tree of tori `G`) has threshold
`p_c(G) = p_c(H~)` and carries the near-critical infinite cluster. The
nonamenability of `H~` lives on the stretched tree edges, which are open only with
probability `q^M`. So a valid proof of any of these holes must use a property of
Cayley graphs that `H~` lacks: transitivity used in a way that no root average
can express.

**Combined with the soft-collapse line.** The soft-collapse nodes keep the Cayley
graph and every soft supercritical property, but lose product structure above
`p_c`, and they collapse. `H~` keeps exact product structure at every parameter,
together with unimodularity, expansion and the Schramm lemma, but loses
transitivity, and it collapses. (The live Russo--BK majorant kill, recorded on
origin/main as fpbs-bk-majorant-integrated-sensitivity-is-critical-l2, rules out one
scheme; this rules out every scheme whose inputs hold on `H~`.) Therefore a proof of `p_c<p_u` through the
walk-rate tip must use exact product structure above `p_c` **and** a
transitive-graph property jointly, at the continuation step. Neither alone
suffices.

**Calibration.**

* On a Cayley graph, root averages equal root values, and every item of Theorem 1
  specializes to known statements: `fpbs-critical-walk-correlation`, the
  `theta^2` floor, and `fpbs-bounded-query-connection-strong-converse`. So nothing
  false is claimed for groups.
* Angel--Hutchcroft remark that "any successful approach to Conjectures 1 and 2
  cannot rely solely on mass-transport arguments". This node makes that remark
  precise for the walk-rate family, and it includes the full product toolbox.

**Paradigm answers.**

* **Why this works where earlier attempts failed.** It changes the host instead of
  the measure. The percolation stays exactly Bernoulli, so the product-structure
  escape left open by the soft-collapse obstructions is closed.
* **First falsifiable step.** The deterministic Cheeger bound for the stretched
  graph from AH's `|d_E K| >= |K|`, and the annealed Schramm lemma by mass transport
  for `p<q`, passed to `p=q` by left-continuity of increasing events.
* **Calibration.** It reproduces the transitive statements, and agrees with the
  published collapse.

**Not claimed.** No statement about Cayley graphs is refuted. Which transitive
property escapes `K` is not identified. The candidate that `H~` visibly violates
is threshold strictness for invariant subgraphs with invariantly amenable
components; it is recorded as a spark, not proved.

## Attempts

- **2026-09-17 (swarm-0917): proof route submitted, class-kill refuted.** Three
  referees checked the route; lens 1 refuted and lenses 2 and 3 survived. All three
  accepted the following: the deterministic Cheeger bound `Phi >= 1/(DM(D+1))`,
  the annealed Schramm lemma `a_n(q) <= rho_bar^n`, the uniqueness floor
  `a_n(p) >= (E_mu_hat theta_p)^2`, the annealed strong converse, the imports from
  arXiv:1710.03003, and the annealed Corollary. The refuted step is the class-kill
  (title, "Class killed", proof Section 6): "any conclusion derived from inputs 1-4
  in root-averaged form holds on H~" comes with no translation lemma, and "run with
  root averages" is not a defined operation. Root averaging does not commute with
  the nonlinear steps Cayley-graph proofs take. Example: on a Cayley graph,
  supermultiplicativity `a_{n+m} >= a_n a_m` follows from Harris-FKG and
  stationarity. In annealed form, `E[tau(o,X_n) tau(X_n,X_{n+m})]` does not split
  into `a_n a_m`. Section 3's own theta^2 floor already needed a new
  operator-positivity proof. So what `H~` refutes is only the listed holes in their
  annealed, root-uniform forms. "Where every member dies" and "product structure
  and transitivity are jointly necessary" depend on the class-kill and are unproven.
  Lenses 2 and 3 flagged the same scoping soft spot. The quenched versions look
  reachable by Borel-Cantelli and the ergodic theorem for the environment. Fix:
  recast the node as a calibration/counterexample node covering only the annealed
  Corollary, or prove a translation lemma.
