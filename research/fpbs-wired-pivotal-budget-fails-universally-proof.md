---
rg: 2
id: fpbs-wired-pivotal-budget-fails-universally-proof
kind: route
title: Integrate Russo from p_c against a two-arm boundary lower bound
target: fpbs-wired-pivotal-budget-fails-universally
requires:
  - fpbs-critical-walk-correlation
  - fpbs-critical-no-infinite-cluster
artifacts:
  - experiments/wired-pivotal-budget-2026-09-17/tree_wired_budget.py
  - experiments/wired-pivotal-budget-2026-09-17/brute_check.py
  - experiments/wired-pivotal-budget-2026-09-17/output-d3.txt
  - experiments/wired-pivotal-budget-2026-09-17/output-d3-large-n.txt
---

Complete written proof. The computation is only a calibration and no step of
the proof uses it. Notation is as in the target claim. The two required
inputs are:

* **(S)** `a_n(p_c) = E P_(p_c)(o <-> X_n) <= rho^n`, from `fpbs-critical-walk-correlation`.
* **(Z)** `theta(p_c) = 0`, from `fpbs-critical-no-infinite-cluster`.

We also use `theta(q) > 0` for `q > p_c`, which is the definition of `p_c`.

Fix `n` and `R >= n`. Put `W_R(x) = {o <-> S_R inside B_R} and {x <-> S_R inside B_R}`
and `E_R(x) = {o <-> x inside B_R}`. Since `|X_n| <= n <= R`, every value `x`
of `X_n` lies in `B_R`.

**Step 0 (positivity).** A geodesic from `o` to `x` lies in `B_n`, which is
contained in `B_R`. So for `q in (0,1)` we have
`a^eps_(n,R)(q) >= a_(n,R)(q) >= E q^(|X_n|) > 0`, and all logarithms below
are finite.

**Step 1 (part 1, Russo).** Condition on `X_n = x` and `xi`. The event
`A^eps` is then an increasing event of the finitely many edges of `B_R`
(there are no edges outside `B_R` in its definition). By Russo's formula,

    d/dq P_q(A | x, xi) = sum_e P_q(e pivotal for A | x, xi).

Here "pivotal" means that `A` occurs with `e` open and fails with `e`
closed. This event does not depend on the state of `e`, so
`P_q(e open and pivotal) = q P_q(e pivotal)`, and an open pivotal edge forces
`A`. Multiplying by `q`, summing over `e`, and averaging over the finitely
many values of `x` and over `xi` gives `q d/dq a^eps = E_q[N^eps ; A^eps]`.
Dividing by `a^eps > 0` proves part 1.

**Step 2 (integration).** Let `M_R(p) = sup_(q in [p_c,p]) E_q[N^eps | A^eps]`.
By part 1,

    log a^eps_(n,R)(p) - log a^eps_(n,R)(p_c) = int_(p_c)^p E_q[N^eps|A^eps] dq/q <= M_R(p) log(p/p_c).     (2.1)

**Step 3 (lower bound above p_c).** Let `p > p_c`. If the cluster of a vertex
`v in B_R` is infinite, then there is an infinite open simple path from `v`.
Its initial segment up to the first vertex of `S_R` uses only vertices of
`B_R`, and edges between them, so `v <-> S_R inside B_R`. (If `v in S_R`,
this holds trivially.) The events `{o <-> infinity}` and `{x <-> infinity}`
are increasing, so Harris–FKG and transitivity give
`P_p(W_R(x)) >= P_p(o <-> infinity, x <-> infinity) >= theta(p)^2`. The coin
is independent of `omega`, so

    a^eps_(n,R)(p) >= eps E P_p(W_R(X_n)) >= eps theta(p)^2 > 0.     (3.1)

**Step 4 (upper bound at p_c).** Volume monotonicity gives
`{o <-> X_n inside B_R}` contained in `{o <-> X_n}`, and `W_R` is contained
in `{o <-> S_R inside B_R}`. Hence

    a^eps_(n,R)(p_c) <= a_n(p_c) + P_(p_c)(o <-> S_R inside B_R) <= rho^n + P_(p_c)(o <-> S_R inside B_R).

The events `{o <-> S_R inside B_R}` decrease in `R`, because a path to
`S_(R+1)` inside `B_(R+1)` passes through `S_R` inside `B_R`. Their
intersection is `{o <-> infinity}`: the cluster meets every sphere, so it is
infinite by local finiteness. By continuity from above and (Z),
`P_(p_c)(o <-> S_R inside B_R) -> theta(p_c) = 0`. Therefore

    limsup_(R -> infinity) a^eps_(n,R)(p_c) <= rho^n     (by (S)).     (4.1)

**Step 5 (part 2).** Combine (2.1), (3.1) and (4.1), using `log(p/p_c) > 0`:

    sup_(R>=n) M_R(p) >= limsup_R M_R(p)
                     >= ( log(eps theta(p)^2) - liminf_R log a^eps_(n,R)(p_c) ) / log(p/p_c)
                     >= ( log eps + 2 log theta(p) + n log(1/rho) ) / log(p/p_c).

This is part 2.

**Step 6 (part 3).** Let `eps_n in [exp(-delta n), 1]` with
`0 <= delta < log(1/rho)`. Fix `p0 in (p_c,1)` and any `p in (p_c,p0]`. The
supremum over `[p_c,p0]` is at least the supremum over `[p_c,p]`. By part 2,

    (1/n) sup_(R>=n) sup_(q in [p_c,p0]) E_q[N^(eps_n)|A^(eps_n)]
        >= ( log(1/rho) - delta + 2 log theta(p) / n ) / log(p/p_c).

Here `theta(p) > 0` is fixed. Letting `n -> infinity` gives the liminf lower
bound `(log(1/rho)-delta)/log(p/p_c)`. This is independent of `n`, and the
numerator is strictly positive. Let `p` decrease to `p_c`: the denominator
tends to `0`, so the liminf is `+infinity`. This proves part 3. In
particular, no `C` satisfies `sup ... <= C n` for all `n`, which is the
failure of (P2) for `A^(eps_n)`.

**Step 7 (part 4).** For fixed `x`,
`A^1_(n,R) \ E_(n,R) = W_R(x) and E_R(x)^c`.

* `W_R(x)` decreases in `R` (Step 4, applied at `o` and at `x`), and its
  intersection over `R` is `{|C(o)| = infinity, |C(x)| = infinity}`.
* `E_R(x)` increases in `R`. Any open path from `o` to `x` is finite, so it
  lies in some `B_R`, and the union of the `E_R(x)` is `{o <-> x}`. Hence
  `E_R(x)^c` decreases to `{o not<-> x}`.

The intersection of two decreasing families decreases to the intersection
of the limits, which is `{C(o), C(x) are distinct infinite clusters}`. By
continuity from above, `a^1_(n,R) - a_(n,R) = P(A^1 \ E)` converges to
`D_n(q)`. This uses a finite average over `x` for each `n`. At a uniqueness
parameter, including every `q` with `theta(q) = 0`, there is almost surely at
most one infinite cluster, so `D_n(q) = 0`.

Now suppose (P2) holds with constants `(C,p0)`, and let `p in (p_c,p0]`.
Integrating (P1) as in (2.1), with `M_R <= Cn`, and using volume monotonicity
and (S), gives

    a_(n,R)(p) <= a_(n,R)(p_c) (p/p_c)^(Cn) <= a_n(p_c) (p/p_c)^(Cn) <= ( rho (p/p_c)^C )^n.

With (3.1) at `eps = 1`, this gives
`a^1_(n,R)(p) - a_(n,R)(p) >= theta(p)^2 - (rho (p/p_c)^C)^n` for every
`R >= n`. Letting `R -> infinity` proves part 4.

**The class statement.** Part 3 is proved using only the properties listed as
"boundary-blind" in the target claim, together with (S) and (Z). Take an
argument each of whose steps remains valid for `A^(eps_n)`. It would prove
`sup <= Cn` for `A^(eps_n)`, which contradicts part 3. Step 2 is the point
where such an argument fails. The two-arm probability of Step 3 is invisible
at `p_c` by (4.1), but at every `q > p_c` it exceeds the linear budget of
free connection.

**The gate.** Two properties are mentioned in the claim.

* Volume monotonicity (Step 4) fails for `A^1`. Indeed,
  `P_q(x <-> y inside B_R/S_R) >= theta(q)^2` for all `x,y in B_R`, so the
  wired two-point operator on `B_R` has norm at least `theta(q)^2 |B_R|` on
  constants. The BK step of `fpbs-l2-gap-gives-bounded-pivotal-counts`
  therefore has no wired analogue.
* Block-chain confinement fails as well. Pivotal edges for `W_R` lie on arms
  from `o` or `x` to `S_R`, off every `o`–`x` path.

**Minimax reframing.** Label the edges of `B_R` by i.i.d. uniform `[0,1]`
labels, so that `omega_q` is the set of edges with label `<= q`. Almost
surely the labels are distinct. The minimax path between `o` and `x` is then
the path in the minimum spanning tree `MST(B_R)`, and `o <-> x` in `omega_q`
if and only if `M_R(o,x) <= q`, where `M_R` is the maximum label on that
path. Hence `a_(n,R)(q)` is the distribution function `F` of `M_R(o,X_n)`,
and (P1) reads `f/F = E_q[N|E]/q`. So (P2) is the reverse-hazard bound
`f/F <= Cn/q` on `[p_c,p0]`. The same identities hold for `B_R/S_R` and
`A^1`, where part 3 shows that the bound fails.

**Calibration (not used above).** On `T_3`, `tree_wired_budget.py` computes
`a` and `a^1` in closed form, with exact derivatives. For a walk endpoint at
distance `k`, the first and last closed geodesic edges split the geodesic,
and the side branches of each geodesic vertex reach `S_R` with probability
`1 - (1 - q u_(R-i-1))^(s_i)`. Here
`u_m = 1 - (1 - q u_(m-1))^2` and `u_0 = 1`. `brute_check.py` verifies the
probability and the conditional pivotal count against full enumeration of
`B_2` and `B_3`. The outputs are in `output-d3.txt` and
`output-d3-large-n.txt`. At `R = 10^5`, the maximum wired count per step on
`[1/2, 0.6]` is:

* `n = 100`: `6.60`, attained at `q - p_c = 7.5e-4`;
* `n = 140`: `18.90`, attained at `q - p_c = 1.8e-4`.

The maximum free count per step is `0.056` and `0.044` respectively.
