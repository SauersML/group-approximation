# Certified replay -- exact optima by a provably admissible integer branch and bound, subgroup values by enumeration, SDP and dominance values by linear programs, and exact rational checks, all asserted by run_census.py

*Attempt artifact (2026-09-17, wave `swarm-0917`), formerly route
`f2-cayley-sse-exact-census-small-k-proof` into
`f2-cayley-sse-exact-census-small-k`, `requires: []`, artifacts
`experiments/sse-small-instances-2026-09-17/{run_census.py, sse_exact.c,
sse_cayley.py, subgroup_dominance.py}`. Demoted from the graph because the
referee stage of this lane produced no verdicts: the census was written as
ESTABLISHED but no referee vote was recorded for it, so it lands agent-written
only, not agent-verified. **No referee refuted it** — no referee read it, and in
particular no one independently audited the admissibility of the branch-and-bound
pruning bound, which is what the exactness of every EXACT value rests on. The
replay `python3 run_census.py` still exits 0 only if every asserted number
reproduces. Restore it as a route once a full referee pass survives.*

## Why sufficient

Every number in the target is recomputed by
`experiments/sse-small-instances-2026-09-17/run_census.py` (parts `A` to `F`).
The script asserts each value and exits `0` only if all of them hold. The
methods are as follows.

**Exact optimum (EXACT).** `sse_exact.c` maximises
`P(S) = sum over unordered pairs u != v in S of w[u xor v]` in integer
arithmetic. Then `stay(S) = 2 P(S)/(W s)`.

- *Translation.* `stay(S + x) = stay(S)`, so it is enough to consider sets
  containing `0`.
- *Enumeration.* Every such set is listed once, in increasing order
  `0 = S_0 < S_1 < ...`, by the depth-first search.
- *Admissible bound.* Suppose `t` elements are chosen, with value `cur`, and
  `r = s - t` remain. The final value is `cur` plus two kinds of terms:
  - *Cross terms.* The pairs (new, old) contribute `sum over new v of gain[t][v]`.
    This is at most the sum of the `r` largest gains among the candidates.
  - *Terms among the new elements.* For a fixed new `v`, its `r - 1` differences
    to the other new elements are distinct nonzero vectors. Their weight is
    therefore at most `topw[r-1]`, the sum of the `r - 1` largest weights.
    Summing over the `r` new elements counts each pair twice, so these terms total
    at most `r topw[r-1]/2`, and hence at most its floor, because the total is an
    integer.

  A branch is cut only when this bound is `<= best`, so no set better than the
  incumbent is lost. The result is the exact maximum.

The numbers are also cross-checked:
- For the s = 4 cases (part C) and the noisy cube (part A), the exact value is
  compared with the subgroup value, computed independently by enumerating
  subspaces in `sse_cayley.py`.
- In part B the exact value is compared with the directly evaluated Hamming ball
  and with the SDP value.

**Subgroup value (SUB).** Every subspace of the given dimension is enumerated
(`sse_cayley.subspaces`), with `Phi(H) = w(H^c)/W`.

**SDP and EIG.**
- *SDP.* For a Cayley graph, the translation-averaged basic SDP is the Delsarte
  linear program in `g(x) = |S n (S + x)|/N`, with the constraints `g(0) = s/N`,
  `sum_x g(x) = s^2/N`, `0 <= g <= g(0)` and `ghat >= 0`. It is solved in
  `sse_cayley.sdp_cert`, and part A accepts it within `5e-4` of the tabulated
  values.
- *EIG.* EIG is the closed-form eigenvalue expression.
- *Ordering.* The asserted strict inequalities `SDP > EXACT + 0.003` and
  `EIG > SDP` are margins far larger than the solver tolerance. All tabulated
  values are asserted to `1e-6`.

**Dominance constants (part E).** `subgroup_dominance.C_theta` solves the linear
program `min t` subject to `sum_H p_H 1[a not in H] <= t d_S(a)`, over all
subgroups of size `s`. For `(4, 8)` it enumerates all `6435` sets containing `0`,
up to the stated normalisation. The witnesses are checked against the rational
values `22/21`, `52/51` and `70/69` to `1e-6`, at the solver's floating-point
accuracy. These are lower bounds on `C*`, and the conclusions use only
`C* >= 22/21 > 1`.

**Part F.** Part F is exact in `Fraction` arithmetic:
- `d_S(a) = 2 Pr_mu[a.y = 1]`;
- `mu(V) <= |V| 2^(-c)` for every subspace `V`;
- the stopped-process miss probability is at most `E_c d_S(a)/2`, through a
  memoised Markov chain over subspaces.

These checks are independent of the analytic proof
`f2-cayley-subgroup-loss-spectral-sampling-proof`.

## Replay

```text
cd experiments/sse-small-instances-2026-09-17
python3 run_census.py            # all parts; prints ALL ASSERTIONS PASSED
python3 run_census.py E F        # a subset
```

The script requires `gcc`, `numpy` and `scipy`, and compiles `sse_exact.c` on
first use. The `k = 7, s = 16` and `k = 8` runs are not part of the replay or the
claim.
