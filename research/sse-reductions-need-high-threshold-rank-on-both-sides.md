---
rg: 2
id: sse-reductions-need-high-threshold-rank-on-both-sides
kind: claim
title: Gap-SSE on regular graphs is decided in time poly(Z, 1/eta) exp(O(R* log R*)) given a cutoff R* on rank_(1-800eta), with two-sided correctness at the ordinary stop, so a reduction from 3SAT whose YES outputs or whose NO outputs all have threshold rank O(log Z / log log Z) gives P = NP, and one whose NO outputs carry poly-bit square certificates gives NP = coNP
distinct_from:
  low-label-threshold-rank-reductions-cannot-prove-ugc: that kills UG reductions only at the YES case, since argmax rounding of a labeling needs completeness; this kills SSE reductions at either side, because accepting a thresholded grid set is sound by a window lemma with no rank promise, and it adds a certificate collapse on the NO side.
  spread-support-overlap-forces-non-expanding-small-sets: that is an unconditional combinatorial kill of NO outputs carrying spread support maps; this is a conditional (P = NP, QP, ETH) spectral kill of either side of low threshold rank, and it touches graphs with no view structure (its survivor H2).
  sticky-cylinder-gadget-compositions-cannot-prove-sseh: that kills fibred compositions over bounded-arity outer chains unconditionally on the NO side; this needs no outer chain and uses only the spectrum of the output graph.
  affine-ug-easy-on-certifiably-hypercontractive-graphs: that imports the BBKSS algorithm for affine UG on certifiably hypercontractive graphs; this is an elementary exact-rational SSE algorithm below a threshold-rank cutoff and a bit-length certificate collapse, and it imports nothing.
  small-set-expansion-hypothesis: that is the open hardness statement; this is a gate on the output graphs of any reduction proving it, and neither proves nor refutes it.
artifacts:
  - experiments/sse-two-sided-rank-gate-2026-09-17/check_two_sided_rank_gate.py
  - research/artifacts/sse-two-sided-rank-gate-attempt-2026-09-17.md
---

**OPEN.** An attempted elementary proof of the whole statement was posted on
2026-09-17 and refuted on 2026-09-18 at the `(G-comb)` bullet of the gate; see
`## Attempts`. Theorems 1--3 below survived three independent re-derivations and
their replay passes, but they are not the whole claim: the gate is part of the
statement, and its combinatorial bullet imports its two sources with the wrong
quantifiers for the regular exact-volume convention used here. The attempt is
kept in full at
`research/artifacts/sse-two-sided-rank-gate-attempt-2026-09-17.md`.

*Setting.* An instance is `(M, s)`, where `M` is a symmetric `n x n` matrix of
nonnegative integers with all row sums equal to `d >= 1` (loops and multi-edges
allowed), and `2 <= s <= n`. Its size `Z` is the bit length. Put `A = M/d` and
`B = (I + A)/2`, and write `e(T) = sum_(u, v in T) M(u, v)`. For `|T| >= 1`,
`1 - Phi(T) = e(T) / (d |T|)`. Then `Gap-SSE_reg(eta, s)` distinguishes:

- **YES:** some `S` with `|S| = s` has `Phi(S) <= eta`;
- **NO:** every `S` with `|S| = s` has `Phi(S) >= 1 - eta`.

This is the regular exact-volume form of `small-set-expansion-hypothesis`, with
`s = delta n`. Let `rank_theta(A)` be the number of eigenvalues of `A` that are
`>= theta`, counted with multiplicity. The invariant is
`R(M) = rank_(1-800 eta)(A)`.

**Theorem 1 (algorithm, two-sided at the ordinary stop).** Given `(M, s)`,
`eta in (0, 1/800]` and a cutoff `R* <= n`, an exact rational algorithm runs in
time `poly(Z, 1/eta) (4 sqrt(2R* + 1)/0.09 + 2)^(2R*)`, plus `n^99 poly(Z)` when
`s < 100`. It outputs "rank above `R*`", ACCEPT or REJECT, and:

1. "rank above `R*`" implies `R(M) > R*`;
2. if `R(M) <= R*`, it does not output "rank above `R*`";
3. at any other output, a YES instance gets ACCEPT (this does **not** need
   `R(M) <= R*`);
4. ACCEPT implies the instance is not NO. This holds always, because ACCEPT
   exhibits a set `T` with `(1 - Phi(T)) kappa(|T|) > eta`, and the window lemma
   turns it into an `s`-set with `1 - Phi > eta`.

**Theorem 2 (two-sided class kill).** Let `Red` be a polynomial-time map from
3SAT formulas to instances `(M, s)` of size `Z`. Satisfiable formulas go to YES
instances of `Gap-SSE_reg(eta, s)` and unsatisfiable formulas to NO instances,
with `eta <= 1/800`. Suppose that **every YES output**, or **every NO output**,
has `R(M) <= R*(Z)`.

- If `R*(Z) = c log Z / log log Z`, then `P = NP`.
- If `R*(Z) = (log Z)^c`, then `NP <= DTIME(exp(O((log Z)^c log log Z)))`, which
  is quasi-polynomial.
- *ETH form.* Suppose `Z <= n^A` for formulas on `n` variables and ETH holds.
  Then for every `alpha < 1/A`, infinitely many YES outputs **and** infinitely
  many NO outputs have `R(M) > Z^alpha`.

The decider runs Theorem 1 with cutoff `R*`. With the YES-side promise it
answers NO on "rank above", and with the NO-side promise it answers YES.
Otherwise it answers ACCEPT / REJECT.

**Theorem 3 (certificate collapse).** A **square certificate** for `(M, s)` is a
rational number `c < 1 - eta` together with rational polynomials `q_j`, `a_u`
and `b` in `x_1, ..., x_n`, written as lists of monomials, such that, as
polynomials,

```text
c d s - sum_(u,v) M(u,v) x_u x_v  =  sum_j q_j(x)^2 + sum_u a_u(x) (x_u^2 - x_u) + b(x) (sum_u x_u - s).
```

Evaluating at `x = 1_S` with `|S| = s` gives `e(S) <= c d s`, so
`Phi(S) >= 1 - c > eta`, and no YES instance has a certificate. If every NO
output of a reduction `Red` as in Theorem 2 has a square certificate of bit length
`<= beta(Z)`, then:

- a polynomial `beta` gives `UNSAT in NP`, so `NP = coNP`;
- a quasi-polynomial `beta` gives `coNP <= NQP`.

This includes every degree-`D` Sum-of-Squares refutation with polynomially many
bits. The algorithmic `n^(O(D))` form needs a bit-complexity bound for SoS on the
slice. That bound is not proved or imported here.

**What dies, and where.**

- *The invariant* is the threshold rank `rank_(1-800 eta)(A)` of the output graph,
  and on the NO side also the bit length of the shortest square certificate.
- *The step.* A small non-expanding set `S` has `||(1_S)_lo||^2 <= s/100` below
  `1 - gamma/8`, with `gamma = 400 eta`. The high part lies within
  `sqrt(s)/100` of the span of `2R*` greedy Gram--Schmidt columns of `B^t`. A grid
  there, thresholded at `1/2`, recovers a set `T` with
  `(1 - Phi(T)) kappa(|T|) >= 0.4915`.
- *Why either side dies.* The UG analogue needs the YES promise, because rounding
  and "rank above" both answer only there. Here the accept rule is sound without
  any promise (item 4). So the "rank above" answer can be given to whichever side
  carries the low-rank promise.

**Class kills.** Under the stated consequences, a proof of SSEH by any
reduction whose output graphs have property P fails when:

- **(K1) low threshold rank on YES outputs.** P is `rank_(1-800 eta) = O(log Z / log log Z)`
  (or polylog, or `Z^(o(1))` under ETH). The reduction dies at the YES output.
  This includes planted-set constructions with few near-1 eigenvalues.
- **(K2) low threshold rank on NO outputs.** P is the same bound on NO outputs.
  The reduction dies at the NO output. This includes small-set expanders with
  polylogarithmically many eigenvalues near `1`, such as noisy-cube-like graphs
  with such a spectrum. So an SSEH reduction must produce NO outputs whose
  threshold rank exceeds every polylogarithm, and under ETH exceeds `Z^alpha` for
  every `alpha < 1/A`.
- **(K3) poly-bit square certificates on NO outputs.** Reductions whose NO graphs
  are certified by constant-degree SoS with polynomially many bits die unless
  `NP = coNP`.

**The gate.** Every reduction proving `small-set-expansion-hypothesis` for
`eta <= 1/800` on regular graphs must pass all of:

- **(G-spec)** infinitely many YES outputs **and** infinitely many NO outputs
  have `rank_(1-800 eta)` above every polylogarithm (above `Z^alpha` under ETH);
- **(G-cert)** NO outputs admit no square certificate of polynomial bit length
  (unless `NP = coNP`);
- **(G-comb)** NO outputs must survive the two unconditional combinatorial kills.
  **This bullet is the refuted part of the claim** (2026-09-18; see
  `## Attempts`). As posted it read "no spread support map with overlap above
  `eta + rho/delta`" and "not fibred over bounded-arity outer chains", which is
  strictly more than the cited theorems give at exact volume. What the sources
  actually license here is:
  - `spread-support-overlap-forces-non-expanding-small-sets`, regular
    exact-volume branch: `eta < (theta - rho/delta)(s - 1)/(10 s)`, so the
    necessary condition is `theta > 10 eta s/(s - 1) + rho/delta`, not
    `theta > eta + rho/delta`. The `(s - 1)/(10 s)` window factor is not
    removable, so an overlap of, say, `2 eta + rho/delta` is **not** killed.
  - `sticky-cylinder-gadget-compositions-cannot-prove-sseh`, regular
    exact-volume branch: `eta + 2 varsigma'(x)/delta < c` with
    `c = k^(-ceil(t/2))`, and that source lists outer arity
    `>= eta^(-1/ceil(t/2))` as an explicit survivor. At `eta = 1/800`, `t = 1`,
    an outer game of arity `k >= 800` survives, so "bounded arity" is not the
    hypothesis, and the exact-volume error term `2 varsigma'/delta` may not be
    dropped.

  Restating the bullet with these quantifiers is the open repair.

Status of known families at the gate:

- 2-to-2 Grassmann test graphs fail (G-comb).
- Graphs like the noisy hypercube, whose threshold rank near `1` is `poly(log n)`,
  are the ABS starting point. If their rank at `1 - 800 eta` is polylogarithmic,
  they fail (G-spec) as NO outputs.
- The Barak--Gopalan--Hastad--Meka--Raghavendra--Steurer graphs
  (arXiv:1111.0405, per the abstract already recorded in
  `small-set-expansion-hypothesis`, "more than `exp(log^delta n)`" eigenvalues
  above `1 - eps`) are small-set expanders with super-polylogarithmic threshold
  rank. They pass (G-spec) at that threshold. Whether they pass (G-cert) was not
  settled here. BBHKSZ (arXiv:1205.4484) is recorded in the graph as showing
  that constant-round SoS certifies small-set expansion for the noisy cube and
  short-code instances. Bit complexity is not addressed there, so (G-cert) is not
  claimed to fail for them.
- **Partial survivor: abelian Cayley graphs, YES side only.** The hypercube
  `Cay(F_2^N, {e_1, ..., e_N})` has eigenvalues `1 - 2|w|/N`, so its rank at
  `1 - 800 eta` is the number of `w` with `|w| <= 400 eta N`, which is
  `2^(Omega(eta log(1/eta) N))`, polynomial in `n = 2^N`. That witness passes
  (G-spec) but it is not a NO instance (its subcubes have `Phi = k/N`, so it is
  never a small-set expander), and the noisy hypercube is also abelian Cayley
  with `rank_(1-800 eta) = polylog(n)` at constant noise, which is exactly what
  (K2) kills as a NO output. So the correct reading is: *some* abelian Cayley
  graphs pass (G-spec) on the YES side; abelian Cayley NO outputs are **not**
  shown to pass. Their (G-cert) status is open either way. (Scoping error
  flagged by the calibration lens, 2026-09-18.)

**Scope.** Only regular graphs with exact volume `s` are treated. The irregular
`[delta, 10 delta]` convention is not covered. The theorems are conditional
kills, not refutations. No citation is used as a proof step. The low-threshold-rank
algorithmic idea is in the Arora--Barak--Steurer line (FOCS 2010), which is not
re-read here, and the proof in the route is self-contained.

The replay script checks:

- the Rayleigh identity, the spectral split and the threshold rounding;
- the window lemma, exhaustively on all subsets for `n = 12`, `s = 4`;
- the greedy stop `m <= max(2R - 1, 0)` and the high-part bound;
- a planted end-to-end run in which the grid finds `rho = 0.938`;
- accept-rule soundness, exhaustively;
- every parameter inequality, for `L <= 4096` and `100 <= s < 5000`;
- the exact rational certificate identity for `c = 1`.

All of these pass. None of them touches (G-comb), which is a statement about two
other nodes' hypotheses, not about this graph algorithm.

## Attempts

**Attempt 1 (2026-09-17, swarm-0917): elementary two-sided threshold-rank
algorithm plus certificate collapse. Refuted 2026-09-18 at (G-comb); returned to
OPEN.** Full text kept at
`research/artifacts/sse-two-sided-rank-gate-attempt-2026-09-17.md`; replay
`experiments/sse-two-sided-rank-gate-2026-09-17/check_two_sided_rank_gate.py`
prints ALL PASS and `bin/cairn check` exits 0.

*What the attempt got.* Theorems 1--3 above, re-derived independently by three
referee lenses with no failing step found. The load-bearing pieces they each
confirmed: the Rayleigh identity and the spectral split
(`||f_lo||^2 <= s eta/(gamma/4) = s/100` at `theta_hi = 1 - 50 eta`); the greedy
stop `m <= max(2R - 1, 0)` via `det G = prod ||v_l||^2 > tau^m` against
`det G <= e_m(mu) <= n^m nu^(m-R)`, valid because `G = (B^(2t))_(J,J)` is a
principal minor of a PSD matrix and `mu_i = lambda_(B,i)^(2t)` — symmetry and the
lazy shift `B = (I+A)/2` are genuinely consumed here, not decorative; the
enabling inequality `nu <= tau^2/n^2`, which is tight (`2 ln 2 = 1.386 < 1.4`);
the high-part bound `-0.7327 L - 9.72 < log2(1/100)`; the dimension-free grid
(`|c_l| <= 1`, `m h^2 s < 0.0081 s`) giving `|T xor S| <= 0.16 s` and
`rho(T) >= 0.84(0.68 - 1/800)/1.16 = 0.4915086 > eta`; the window lemma in both
branches, including `s/t >= s(s-1)/(t(t-1))` for loops when `t >= s`; the Cramer
bit bounds; and the ETH finite-table argument, sound because YES and NO outputs
are disjoint at `eta <= 1/800`.

*Why it does not establish the claim.* The gate is part of the statement, and the
`(G-comb)` bullet imports both of its sources with the wrong quantifiers for the
regular exact-volume convention declared in *Scope*:

1. *Spread overlap.* `spread-support-overlap-forces-non-expanding-small-sets`
   states its class kill in two separated branches, and the attempt quoted the
   `[delta, 10 delta]` branch (`eta < theta - rho/delta`) while working in the
   exact-volume branch (`eta < (theta - rho/delta)(s - 1)/(10 s)`). The
   `(s - 1)/(10 s)` factor is the window cost of moving a zoom set of measure in
   `[delta, 10 delta]` to exact volume `s`, so it cannot be dropped. The true
   necessary condition is `theta > 10 eta s/(s - 1) + rho/delta`. A reduction
   whose NO outputs carry overlap `2 eta + rho/delta` was declared dead and is
   not.
2. *Sticky cylinders.* `sticky-cylinder-gadget-compositions-cannot-prove-sseh`
   requires `eta + 2 varsigma'(x)/delta < c` with `c = k^(-ceil(t/2))` in the
   exact-volume branch, and explicitly lists outer arity
   `>= eta^(-1/ceil(t/2))` as a survivor. At `eta = 1/800`, `t = 1`, arity
   `k >= 800` survives. So "bounded arity" is not the cited hypothesis, and the
   exact-volume error term was dropped.

Both halves were labelled "This part is unconditional", and the error had already
propagated to the attempts entry in `small-set-expansion-hypothesis`. Both places
are now corrected to what the sources license.

*Also corrected, separately.* The abelian-Cayley "survivor" annotation was scoped
to the YES side only: the hypercube witness is not a NO instance, and the noisy
hypercube is an abelian Cayley graph that (K2) kills as a NO output.

*What is left to do.* Restate `(G-comb)` with the exact-volume quantifiers above
and re-check that the resulting gate is still non-vacuous; then the rest of the
attempt is available unchanged as the route.
