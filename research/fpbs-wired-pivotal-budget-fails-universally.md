---
rg: 2
id: fpbs-wired-pivotal-budget-fails-universally
kind: claim
title: The wired-ball pivotal budget fails on every nonamenable Cayley graph, even at exponentially small wiring weight
distinct_from:
  fpbs-hierarchical-pivotal-amplification: that has unbounded counts on nontransitive finite networks at one fixed parameter far from p_c; this keeps the true Cayley geometry at every interior vertex and the true critical window, changes only the boundary condition on the sphere S_R, and fails on every nonamenable Cayley graph, trees included.
  fpbs-msf-excess-equals-nonuniqueness: that is the infinite-volume integral identity for the free-minus-wired forest degree at an edge; this is a finite-volume boundary-condition statement for the random-walk pivotal budget, with the R-limit free/wired gap identified as the distinct-infinite-cluster probability of o and X_n at one parameter.
  fpbs-expander-approximant-giant-data-is-glued: that concerns finite expander approximants converging locally to G; this concerns the induced balls of G itself, where the free boundary holds the budget on trees and the wired boundary violates it.
  fpbs-l2-gap-gives-bounded-pivotal-counts: that proves the free budget under critical l2 boundedness, using volume monotonicity in its BK step; this shows the same statement with a wired boundary is false on every graph, so that monotonicity step is load-bearing.
  fpbs-tree-walk-pivotal-count-bounded-below-l2-threshold: that computes the free count on T_d (at most n for every p); here the wired count on T_d is superlinear near p_c.
artifacts:
  - research/fpbs-wired-pivotal-budget-fails-universally-proof.md
  - experiments/wired-pivotal-budget-2026-09-17/tree_wired_budget.py
  - experiments/wired-pivotal-budget-2026-09-17/brute_check.py
  - experiments/wired-pivotal-budget-2026-09-17/output-d3.txt
  - experiments/wired-pivotal-budget-2026-09-17/output-d3-large-n.txt
  - experiments/wired-pivotal-budget-2026-09-17/output-brute-check.txt
---

**Obstruction (class-killing calibration for `fpbs-pivotal-budget-universal`).**

**Setting.** `G = Cay(Gamma,S)` is a nonamenable locally finite Cayley graph
with root `o` and spectral radius `rho<1`. `X_n` is simple random walk from
`o`, independent of Bernoulli(`q`) bond percolation `omega`. For `R>=n`,
`B_R` is the induced ball, `S_R` its sphere, and
`E_(n,R) = {o <-> X_n inside B_R}` is the free event of (P2). For
`eps in [0,1]` let `xi` be an independent Bernoulli(`eps`) coin and put

    A^eps_(n,R) = E_(n,R)  union  ( {xi=1} and {o <-> S_R inside B_R} and {X_n <-> S_R inside B_R} ).

`A^1` is connection in the wired ball `B_R/S_R`. `N^eps` counts the open
pivotal edges of `B_R` for `A^eps` (the coin is not an edge). Write
`a^eps_(n,R)(q) = P_q(A^eps_(n,R))`, `a_n(q) = P_q(o <-> X_n)`, and
`theta(q) = P_q(o <-> infinity)`.

**Theorem.**

1. **(Russo.)** For `q in (0,1)`,
   `q d/dq log a^eps_(n,R)(q) = E_q[N^eps_(n,R) | A^eps_(n,R)]`.
2. **(Quantitative failure.)** For every `n>=1`, `p in (p_c,1)` and
   `eps in (0,1]`,

       sup_(R>=n) sup_(q in [p_c,p]) E_q[N^eps_(n,R) | A^eps_(n,R)]
           >=  ( n log(1/rho) + log eps + 2 log theta(p) ) / log(p/p_c).

3. **(No linear budget, whatever the constant.)** Let `0 <= delta < log(1/rho)`
   and `eps_n >= exp(-delta n)`. For every `p0 in (p_c,1)`,

       lim_(n -> infinity) (1/n) sup_(R>=n) sup_(q in [p_c,p0]) E_q[N^(eps_n)_(n,R) | A^(eps_n)_(n,R)] = +infinity.

   So the budget (P2) with `A^(eps_n)` in place of `E_(n,R)` fails for every
   `C` and `p0`. This includes the fully wired ball (`eps=1`) and wiring
   weights exponentially small in `n`.
4. **(The free/wired gap is the distinct-cluster probability.)** For every `q`
   and `n`,
   `lim_(R -> infinity) ( a^1_(n,R)(q) - a_(n,R)(q) ) = D_n(q) := E P_q(o and X_n lie in distinct infinite clusters)`.
   Hence `D_n(q) = 0` at every uniqueness parameter, and the free budget (P2)
   with constants `(C,p0)` forces `D_n(p) >= theta(p)^2 - (rho (p/p_c)^C)^n`
   for `p in (p_c,p0]`.

**Where every member of the class dies.** Call an argument for (P2)
*boundary-blind* if each of its steps stays valid when `E_(n,R)` is replaced
by `A^(eps_n)_(n,R)` for some `eps_n >= exp(-delta n)`, `delta<log(1/rho)`.
Such steps include:

* the finite-volume Russo identity;
* Harris–FKG and BK/Reimer inside `B_R` (the pair `(omega,xi)` is still a
  product measure and `A^eps` is increasing);
* uniformity in `R`;
* the interior geometry, transitivity and nonamenability of `G`;
* infinite-volume inputs at `p_c`: Schramm's lemma, `theta(p_c)=0`, and any
  bound on `tau_(p_c)`.

By part 3, every boundary-blind argument proves a false statement. It dies at
the integration step from `p_c` to `q>p_c` taken uniformly in `R`. The
invariant it cannot see is the two-arm boundary probability
`P_q(o <-> S_R, X_n <-> S_R inside B_R)`. This tends to `0` at `p_c` and is at
least `theta(q)^2 > 0` for every `q>p_c`.

**The gate.** A proof of (P2) must, at some parameter above `p_c`, use a
property of the free event that fails for `A^eps`. Two such properties are
known:

* *Volume monotonicity* `P_q(x <-> y inside B_R) <= tau_q(x,y)`, used in the
  BK step of `fpbs-l2-gap-gives-bounded-pivotal-counts`. The wired analogue
  gives `||T||>=theta^2 |B_R|`.
* *Confinement of pivotal edges to the block chain between `o` and `X_n`*, as
  in `fpbs-cactus-finite-ball-pivotal-budget`. For `A^eps`, pivotal edges sit
  on arms to `S_R`.

Both known positive proofs therefore lie outside the class, as they must.
Part 4 says what the free boundary buys in the limit: exactly the probability
`D_n` that `o` and `X_n` lie in distinct infinite clusters, the finite-volume
shadow of the FMSF/WMSF excess of `fpbs-msf-excess-equals-nonuniqueness`. The
two-point state family of the group-rings lease had pointed at "only the
finite ball truncation" as the separating input. This refines that diagnosis:
truncation with a wired boundary does not separate, and what separates is the
free, volume-monotone truncation.

**Minimax reframing.** Give edges i.i.d. uniform labels. Then
`o <-> x inside B_R` in `omega_q` iff the maximum label `M_R(o,x)` on the
minimum-spanning-tree path of `B_R` is at most `q`. So (P2) says that the
reverse hazard rate `f/F` of `M_R(o,X_n)` is at most `Cn/q` on `[p_c,p0]`.
The wired statement is the same bound for the MST of `B_R/S_R`, and it fails.

**Calibration on `T_3`** (`p_c=1/2`, `rho=2 sqrt 2/3`; exact closed forms
checked by brute force on `B_2` and `B_3`). The table gives
`max over q in [p_c,0.6]` of the conditional count divided by `n`:

| `n` | free (any `R`) | wired, `R=10^2` | wired, `R=10^5` | argmax `q-p_c` |
|---|---|---|---|---|
| 10 | 0.211 | 1.000 | 1.008 | 3.2e-2 |
| 20 | 0.148 | 1.024 | 1.105 | 1.8e-2 |
| 40 | 0.100 | 1.111 | 1.580 | 7.5e-3 |
| 60 | 0.078 | 1.121 | 2.462 | 3.2e-3 |
| 100 | 0.056 | (`R=10^3`: 4.767) | 6.601 | 7.5e-4 |
| 140 | 0.044 | (`R=10^3`: 6.161) | 18.901 | 1.8e-4 |

The free count stays below `n` (and (P2) holds with `C=1`). The wired count
per step grows, and its maximiser moves toward `p_c`, as part 3 predicts.

Proof: `fpbs-wired-pivotal-budget-fails-universally-proof`.
