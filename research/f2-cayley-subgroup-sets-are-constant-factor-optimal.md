---
rg: 2
id: f2-cayley-subgroup-sets-are-constant-factor-optimal
kind: claim
title: There is an absolute constant C such that every set S of size 2^j in F_2^k has subgroup-dominance constant C(S) <= C, so in every weighted Cayley graph of F_2^k some subgroup of size |S| has Phi <= C Phi(S)
distinct_from:
  f2-cayley-subgroup-sets-lose-at-most-log-inverse-density: that proves C(S) <= E_c/2 = Theta(log(1/delta)); this asks for a bound independent of delta and k, which is what removes the log(1/delta) regime where SSEH lives.
  small-set-expansion-hypothesis: that is hardness for general graphs; this is an approximation statement on F_2^k Cayley graphs whose truth would make that class easy at every measure (route f2-cayley-gap-sse-by-subgroup-enumeration).
  spread-support-overlap-forces-non-expanding-small-sets: that finds non-expanding sets from spread support maps and leaves the noisy cube as survivor (H1); this concerns abelian Cayley graphs and compares non-expanding sets with subgroups.
artifacts:
  - experiments/sse-small-instances-2026-09-17/subgroup_dominance.py
  - experiments/sse-small-instances-2026-09-17/run_census.py
---

**OPEN.** Notation is as in `f2-cayley-subgroup-sets-lose-at-most-log-inverse-density`.
For `|S| = s = 2^(k-c)` and `d_S(a) = |S \ (S+a)|/s`,

```text
C(S) = min over distributions p on subgroups H with |H| = s  of  max_(a != 0) Pr_p[a not in H] / d_S(a)
     = sup over weight laws w of  min_H Phi_w(H) / Phi_w(S)          (LP duality, proved there).
```

**Conjecture.** `C* := sup_(k, c, S) C(S) < infinity`.

*Weak form* (enough for the algorithmic consequence). There is a function `F`
with `F(eta) -> 0` as `eta -> 0`, independent of `k` and `c`, such that
`Phi_w(S) <= eta` implies `min_(|H| = s) Phi_w(H) <= F(eta)`.

It is a **fractional Harper inequality for all generating laws at once**. For `w`
supported on a linearly independent set, it holds with `C = 1`. After a change of
basis, Harper's edge-isoperimetric inequality gives `sum_i d_S(e_i) >= c`, and the
best subgroup of index `2^c` pays exactly the `c` smallest weights. The
conjecture asks that dependent generator laws, like vectors of weight `<= 2` or
noise laws, lose only a constant.

**Established facts toward it.**

- *Lower bound.* `C* >= 22/21`, attained by the Hamming ball `{0, e_1, ..., e_7}`
  in `F_2^7`. The same value is also found at `(k, s) = (6, 8)` by local search.
  `C(S) >= 1` always, since uniform `w` gives every set of size `s` the same
  `Phi`.
- *Upper bound.* `C(S) <= E_c/2 <= (c + 1.61)/2` (the log-loss claim). `C(S) = 1`
  when `c = 1`.
- *Size 4.* `C(S) = 1` for `|S| = 4`, at every `k`. If `S = {0, a, b, c}` is not a
  subgroup, its six differences lie on the four 2-dimensional subgroups
  `<a,b>`, `<a,c>`, `<b,c>`, `<a+b, a+c>`, each difference on exactly two. With `p`
  uniform on these four, `Pr[x not in H] = 1/2 = d_S(x)` for each difference `x`.
  Every other `x` has `d_S(x) = 1`.
- *Tensorization (proved here).* `C(S_1 x S_2) <= max(C(S_1), C(S_2))` in
  `F_2^(k_1) x F_2^(k_2)`. Use product distributions: with
  `q_i = min(1, C d_i)` and `C >= 1`,
  `1 - (1 - q_1)(1 - q_2) <= C (1 - (1 - d_1)(1 - d_2))`.
  If both `C d_i <= 1` this follows from `C^2 d_1 d_2 >= C d_1 d_2`. Otherwise the
  left side is `1 <= C d_1 <= C (d_1 + d_2 - d_1 d_2)`. So product constructions
  cannot drive `C*` up.
- *Data* (certified by `run_census.py E`). The maximum is `1` over all 6435 sets
  at `(k, s) = (4, 8)`. Local search (400 steps, two seeds, `subgroup_dominance.py search`)
  gives maxima `52/51` at `(5, 8)`, `22/21` at `(6, 8)` and `70/69` at `(6, 16)`.
  The proved bound at those points is `1.67`, `2.24` and `1.67`.

**Why it matters.** If the conjecture holds, `Gap-SSE(eta, delta)` on `F_2^k`
Cayley graphs is decided by enumerating subgroups for every `eta < 1/(1 + C*)`
and every dyadic `delta` (`gap-sse-on-f2-cayley-graphs-is-polynomial`). Then no
SSEH reduction can output such graphs, which kills the abelian-Cayley survivor
of the live-bus lemma `sse-reductions-need-high-threshold-rank-on-both-sides`. If
it fails, the failure itself is structural: an SSEH-hard `F_2^k` Cayley family
needs sets `S` with `C(S) >= (1 - eta)/eta`. These would be non-expanding sets
that no mixture of subgroups tracks, which is new behaviour for abelian groups.

**Attack routes.**

- Polynomial Freiman--Ruzsa (Gowers--Green--Manners--Tao) applied to the
  approximate symmetry sets `A_theta = {a : d_S(a) <= theta}`. These satisfy
  `A_theta + A_theta <= A_(2 theta)` and `|A_theta| <= s/(1 - theta)`. Restricting
  the max in `C(S)` to `A_theta` loses only `1/theta`:
  `Phi(H) <= (C_theta(S) + 1/theta) Phi(S)`.
- Improve the stopping-time argument. The log loss comes from charging every
  sample, and the census suggests most samples are harmless.
- Search at `k >= 8` with a column-generation LP over subgroups. The open
  question is whether `C` grows with `c`.

## Attempts

* **Spectral sampling (2026-09-17, swarm-0917, compute-scout).** Sample
  characters from `mu_S` until they span dimension `c`, as in the attempt
  artifact
  `research/artifacts/f2-cayley-subgroup-loss-spectral-sampling-proof-2026-09-17.md`
  (drafted for `f2-cayley-subgroup-sets-lose-at-most-log-inverse-density`, not
  refereed).
  - *Where it dies.* It charges `d_S(a)/2` for every sample, including the
    samples that do not raise the dimension. The expected number of samples is
    `E_c ~ c`, so the constant is `E_c/2`, not an absolute constant.
  - *What would repair it.* Charge only the dimension-raising samples, which
    needs `Pr[a.y = 1 | y not in V] <= C d_S(a)` uniformly over the stopped
    subspaces. That bound is not proved here. Conditioning on `y not in V`
    can move mass toward characters that are odd on `a`, and the mass bound (2)
    controls only `mu(V)`, not how the remaining mass splits across `a`.
* **Local search for counterexamples (same wave).** The method is
  `subgroup_dominance.py search` (400 steps, two seeds) at `(5, 8)`, `(6, 8)` and
  `(6, 16)`, together with the exhaustive run at `(4, 8)`.
  - *Result.* The largest value found is `22/21`.
  - *Where it dies.* The search cannot reach `k >= 8`, because the number of
    subgroups in the LP grows as `2^(c(k-c))`.
