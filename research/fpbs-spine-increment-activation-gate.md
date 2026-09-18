---
rg: 2
id: fpbs-spine-increment-activation-gate
kind: claim
title: For collapse families over a connected label-independent spine, the operator gate reduces exactly to one fully annealed estimate, that the Bernoulli-sandwiched spine two-point increment is at most an atomless measure times X J X, and every collapse family violates it
distinct_from:
  fpbs-quenched-bk-russo-collapse-operator-gate: that gate (G) is stated in plain volumes, with left-limit atoms, and compares the full annealed increment with T J T; this gate is stated in spine-augmented volumes with a right-endpoint atomless measure, and only the spine increment beta (S_t - S_s) beta is compared, since the Russo part is already controlled
  fpbs-continuous-activation-collapse-family: that proves (G) fails in its density term for one family; this proves the failure is in the activation part, which reduces to the explicit spine increment, for every collapse family over a connected label-independent spine starting from the empty set
  fpbs-annealed-pivotal-factorization-off-spine-bridges: that proves the split bounds (R) and (A); this integrates them into a gate and derives the obstruction
---

**ESTABLISHED (class-killing obstruction; the reduced gate).** Proof in
`fpbs-spine-increment-activation-gate-proof`.

**Setting.** As in `fpbs-annealed-pivotal-factorization-off-spine-bridges`:
`omega_r = xi_r ∪ Z_r` on `[t_0,t_1]` with a connected label-independent
environment `(Z_r)`. `X^Lambda_r(u,v) = P(u <-> v in omega_r ∩ (Lambda ∪ Z_r))` is
the spine-augmented kernel on `W = V(Lambda)`. `beta^Lambda_r` is the Bernoulli
kernel of `Lambda`, and `S_r(x,y) = P(x,y in V(Z_r))` is the spine two-point
function. Assume `Z_{t_0} = ∅`, so the spine grows from nothing, and
`||T_{t_0}||_{2->2} < infinity`, where `T_{t_0}` is the Bernoulli two-point
function at `t_0`.

**Theorem 1 (right-endpoint atomless gate).** Let `W` be finite and let
`(X_t)_{t in [t_0,t_1]}` be nonnegative `W × W` matrices with unit diagonal,
entrywise nondecreasing in `t`. Let `kappa` be a finite atomless Borel
measure. Suppose `X_t - X_s <= kappa((s,t]) X_t J_W X_t` entrywise for all
`s < t`. Then `1/||X_s|| - 1/||X_t|| <= d kappa((s,t])`.

Consequently, suppose a family of such matrices `X^{(j)}_t`, indexed by an
exhaustion, increases pointwise to a kernel `T_t`, and each `X^{(j)}_{t_0}` is
entrywise below the compression of `T_{t_0}`. Then `d ||T_{t_0}|| kappa((t_0,t]) < 1`
implies `||T_t|| <= ||T_{t_0}|| / (1 - d ||T_{t_0}|| kappa((t_0,t]))`.

**The reduced gate.** Fix an exhaustion `Lambda_j ↑ E` and a finite atomless
measure `kappa_A` on `[t_0, t_0 + delta]`. The gate is

```text
(AG*)  beta^{Lambda_j}_s (S_t - S_s) beta^{Lambda_j}_s <= kappa_A((s,t]) X^{Lambda_j}_t J_W X^{Lambda_j}_t
       for all j and all t_0 <= s < t <= t_0 + delta.
```

Its weaker, non-explicit form (AG) replaces the left side by the activation
increment `D^A_{s,t}`.

**Theorem 2 (sufficiency).** If (AG*), or only (AG), holds, then for every
`t in (t_0, t_0+delta]` with `d ||T_{t_0}|| (2(t-t_0) + kappa_A((t_0,t])) < 1`,

```text
||T_t|| <= ||T_{t_0}|| / (1 - d ||T_{t_0}|| (2(t - t_0) + kappa_A((t_0,t]))) < infinity .
```

In particular `inf_{u,v} T_t(u,v) = 0` on an infinite graph, so `omega_t` is
not FKG-unique there.

**Corollary 3 (every collapse family violates the reduced gate).** Suppose in
addition that `inf_{u,v} T_t(u,v) > 0` for all `t in (t_0, t_0+eps)`. The
continuous-activation family of `fpbs-continuous-activation-collapse-family`
on a critical-L2 spine graph is an example: there `t_0 = p_c`,
`T_t >= theta_xi(t)^2`, and `Z_{p_c} = ∅`. Then for every `delta > 0`, every
exhaustion and every finite atomless `kappa_A`, (AG) fails, and hence (AG*)
fails.

The Russo part obeys `D^R <= 2 (t-s) X J X` in these volumes, with no
bridges. So the whole obstruction is the single explicit kernel inequality
(AG*). Its left side is built only from the Bernoulli kernel of `Lambda` and
the law of the spine. No quenched correlations are involved.

**Class killed.** Take an argument for `p_c < p_u` on critical-L2 spine
graphs. Suppose that above `p_c` it uses only the inputs listed as killed in
`fpbs-continuous-activation-collapse-family`, together with:

* the exact annealed pivotal factorization `D^R <= 2 (t-s) X J X`, or
  `R <= 2 T J T` off bridges;
* any control of activations weaker than (AG*).

Then it proves a false statement. A correct argument must contain an input
that implies (AG*) along some exhaustion: a bound on the spine two-point
increment, sandwiched between Bernoulli kernels, by `X J X` with an
integrable rate. For Bernoulli percolation `S ≡ 0`, and (AG*) is trivial.

**Mechanism (heuristic, not proved).** `S_{t_0} = 0` while `S_t > 0` for
`t > t_0`. The diagonal of the left side of (AG*) contains
`beta(u,x) (S_t - S_s)(x,x) beta(x,v)`. Compared with the part of `X_t`
routed through the spine, the ratio behaves like the relative increment
`(S_t - S_s)/S_t`, and `∫_{t_0} dS/S = infinity`, a logarithmic divergence.
Starting the gate at `t_0' > t_0`, where `S_{t_0'} > 0`, would make the rate
integrable, but then `||T_{t_0'}|| = infinity`. A collapse family trades a
finite starting norm for a log-divergent activation rate.

**Next step (open).** Prove the log law: for the continuous-activation family,
the minimal `kappa_A` in (AG) satisfies
`kappa_A((s,t]) >= c log(m(t)/m(s))`, where `m(r) = P(o in V(Z_r))`. Then show
the converse: any invariant input excluding a log-divergent spine growth
from `∅` implies (AG*). That would make (AG*) the exact Bernoulli-specific
input that a proof of `p_c < p_u` must supply.
