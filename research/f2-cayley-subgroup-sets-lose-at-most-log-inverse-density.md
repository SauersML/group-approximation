---
rg: 2
id: f2-cayley-subgroup-sets-lose-at-most-log-inverse-density
kind: claim
title: In every weighted Cayley graph of F_2^k, every set S of measure 2^-c has a subgroup H with |H| = |S| and Phi(H) <= (E_c/2) Phi(S), where E_c = sum_(i<=c) 1/(1-2^-i) <= c + 1.61, so Gap-SSE(eta, 2^-c) on these graphs is decided by subgroup enumeration in time N^(c+O(1)) once eta (c + 3.61) < 2
distinct_from:
  elementary-abelian-galois-games-round-with-linear-loss: that rounds an SDP certificate of a Galois game to a transversal subgroup complement with loss O(eps log k); this compares an arbitrary non-expanding set (no certificate, no transversality) with a subgroup of the same size, samples subgroups from the set's own spectral measure, and gives the constant E_c/2, which is exactly 1 at measure 1/2.
  small-set-expansion-hypothesis: that is the open hardness statement for all graphs; this is an unconditional approximation theorem on one graph class, and it only forces hard Cayley families into the regime eta log(1/delta) >= 2 - o(1).
  f2-cayley-subgroup-sets-are-constant-factor-optimal: that conjectures a factor independent of c; this proves the factor E_c/2 = Theta(c).
artifacts:
  - experiments/sse-small-instances-2026-09-17/run_census.py
  - experiments/sse-small-instances-2026-09-17/subgroup_dominance.py
---

**OPEN.** A self-contained direct proof was drafted on 2026-09-17 and is kept as
an attempt (see Attempts). It is not established because the lane's referee stage
recorded no verdict on it: no referee refuted it, and no referee read it. The
statement below is what that attempt claims, not what the graph asserts.

*Setting.* `N = 2^k`. A weighted Cayley graph `Cay(F_2^k, w)` has weights
`w_a >= 0` on nonzero `a`, total `W`, and vertex `x` joined to `x + a` with
weight `w_a`. For `|S| = s` put `d_S(a) = |S \ (S + a)|/s`. Then

```text
Phi(S) = sum_a w_a d_S(a) / W,     and for a subgroup H:  Phi(H) = w(F_2^k \ H) / W.
```

**Theorem.** Let `s = 2^(k-c)` and `E_c = sum_(i=1)^c 1/(1 - 2^(-i))`, so
`E_1 = 2`, `E_2 = 10/3`, `E_3 = 4.476...`, and `E_c <= c + 1.607`.

1. *(Subgroup dominance.)* For every `S` with `|S| = s` there is a probability
   distribution `p` on subgroups `H` with `|H| = s` such that
   `Pr_p[a not in H] <= (E_c/2) d_S(a)` for every nonzero `a`. Equivalently, the
   **subgroup-dominance constant**
   `C(S) = min_p max_(a != 0) Pr_p[a not in H] / d_S(a)` satisfies
   `C(S) <= E_c/2`.
2. *(Weight-free transfer.)* Hence in every weighted Cayley graph of `F_2^k`,
   `min_(|H| = s) Phi(H) <= C(S) Phi(S) <= (E_c/2) Phi(S)`. By LP duality `C(S)`
   is exactly `sup_w min_H Phi(H)/Phi(S)` over all weight laws `w` with
   `Phi_w(S) > 0`, so no weight-dependent argument can do better than `C(S)`.
3. *(Algorithm.)* On weighted Cayley graphs of `F_2^k` given by their weight
   table (input size `N`), `Gap-SSE(eta, 2^(-c))` (distinguish
   `Phi_G(2^-c) <= eta` from `Phi_G(2^-c) >= 1 - eta`) is decided in time
   `N^(c + O(1))` whenever `(E_c/2) eta < 1 - eta`, for instance whenever
   `eta (c + 3.61) < 2`. The algorithm accepts iff some subgroup of index `2^c`
   carries weight at least `W (1 - (E_c/2) eta)`.
4. *(Half measure.)* At `c = 1` the factor is `1`: `Phi_G(1/2)` is attained by a
   hyperplane. This is consistent with the spectral bound
   `Phi(S) >= (1 - lambda_2)(1 - mu(S))`.

*Mechanism.* `d_S(a) = 2 Pr_(y ~ mu_S)[a . y = 1]` for the spectral measure
`mu_S(y) = N |1_S^(y)|^2 / s`, a probability measure whose mass on any subspace
`V` is at most `|V| 2^(-c)` (Poisson summation). Sample `y_1, y_2, ...` iid from
`mu_S` until they span a `c`-dimensional `V`, and take `H = V^perp`. While
`dim V = j < c` a sample is new with probability at least `1 - 2^(j-c)`, so the
stopping time has mean at most `E_c`. `a` leaves `H` only if some sample has
`a . y_i = 1`, so Wald's identity gives `Pr[a not in H] <= E_c d_S(a)/2`.

**Numbers (certified by `run_census.py`, parts E and F).**

| `(k, s, c)` | `E_c/2` | largest `C(S)` found |
|---|---|---|
| `(4, 8, 1)` | `1` | `1` (all 6435 sets) |
| `(k, 4, k-2)`, any `k` | `E_(k-2)/2` | `1` exactly (four-lines argument; census claim) |
| `(5, 8, 2)` | `1.667` | `52/51` (local search) |
| `(6, 8, 3)` | `2.238` | `22/21` (local search) |
| `(6, 16, 2)` | `1.667` | `70/69` (local search) |
| `(7, 8, 4)` | `2.771` | `22/21` (Hamming ball `{0, e_1..e_7}`) |

The replay also checks, in exact rational arithmetic on random sets with
`k <= 5`, the identity `d_S(a) = 2 Pr_mu[a.y = 1]`, the subspace mass bound, and
(for `k <= 4`) the exact miss probability of the sampled subgroup against
`E_c d_S(a)/2`.

**What this does and does not kill.** An SSEH-hard family of `F_2^k` Cayley
graphs (with `P != NP`) must, for each small `eta`, use measures
`delta <= 2^(-(2/eta - 3.61))`. That is the regime
`eta log_2(1/delta) >= 2 - O(eta)`, which is where the noisy cube already lives.
So it kills nothing by itself. The gap between the proved factor `Theta(c)` and
the observed factor `<= 22/21` is the open claim
`f2-cayley-subgroup-sets-are-constant-factor-optimal`. A constant factor would
remove `F_2^k` Cayley graphs as SSEH-hard outputs at every measure. This is the
survivor "abelian Cayley (rank n^Omega(1))" named on the live bus by
`sse-reductions-need-high-threshold-rank-on-both-sides`, a node that is not in
this checkout. The novelty check was bounded: a web search found no
subgroup-versus-set statement for general Cayley graphs of `F_2^k`.

## Attempts

1. **Spectral-measure subgroup sampling (2026-09-17, wave `swarm-0917`; drafted
   complete, never refereed).** Formerly route
   `f2-cayley-subgroup-loss-spectral-sampling-proof`, `requires: []`. The proof is
   kept as the attempt artifact
   `research/artifacts/f2-cayley-subgroup-loss-spectral-sampling-proof-2026-09-17.md`,
   together with `experiments/sse-small-instances-2026-09-17/run_census.py`.

   - *Reason it is not established.* The lane wrote it as ESTABLISHED, but its
     referee stage returned no verdicts at all — the votes were lost, not cast
     against it. Under the program's rule that only a route no referee could
     refute establishes a claim, a route with zero referee reads does not
     qualify, so the claim returns to OPEN and the proof lands as an attempt.
     **No referee found a gap**; none looked.
   - *What the attempt argues.* `d_S(a) = 2 Pr_mu[a.y = 1]` for the spectral
     measure `mu = N fhat^2/s`; Poisson summation gives `mu(V) <= |V| 2^-c` for
     every subspace `V`; drawing characters from `mu` until they span dimension
     `c` and taking `H` as the annihilator stops after at most `E_c` draws in
     expectation, and Wald's identity converts this into
     `Pr[a not in H] <= (E_c/2) d_S(a)`.
   - *Independent support.* Part F of `run_census.py` verifies the three steps in
     exact rational arithmetic for `k <= 5` (and the exact miss probability for
     `k <= 4`). This is evidence, not a referee pass: it checks the identities the
     attempt uses, not the attempt's own reasoning.
   - **To restore:** run a full adversarial referee pass (proof-gap lens and
     citation/hypothesis-match lens) over the attempt artifact and, if both
     survive, restore it as a route with `target` and `requires: []` unchanged.
