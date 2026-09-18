---
rg: 2
id: qudit-weyl-rounding-constant-2d-over-sqrt3-pi-via-trace-norm
kind: route
title: Commuting-set rounding succeeds iff a threshold vector is in STAB of the noncommutation graph, and the commutator-Gram trace norm puts it there given the Hermitian edge inequality
target: qudit-weyl-rounding-constant-is-2d-over-sqrt3-pi
requires:
  - hermitian-edge-trace-norm-vs-independence
  - qudit-weyl-rounding-one-qudit-constant-is-2d-over-sqrt3-pi
  - qudit-weyl-rounding-constant-linear-upper-bound
  - qudit-weyl-rounding-constant-triangular-harper-bound
artifacts:
  - experiments/qudit-weyl-rounding-multiqudit-2026-09-18/README.md
---

Ordinary proof of the implication, unreviewed, not Lean-verified. Lane w5-078, 2026-09-18.

**What is proved here.** `hermitian-edge-trace-norm-vs-independence` (**) implies
`c_d <= c*(d) <= 2d/(sqrt3 pi) + 4 + 1.21/d` on any number of qudits, for prime `d >= 5`. With
the lower bound of `qudit-weyl-rounding-constant-triangular-harper-bound`, this gives
`c_d = 2d/(sqrt3 pi) + O(1)`. Only the matrices `C` of Lemma L are fed into (**). So the weaker
"Weyl" instance of (**) is enough: `C_ij = (1 - omega^(t_ij)) z_ij / (2 sin(pi/d) eta)`. The
converse (that (**) is needed) is not claimed.

## Setting

`n` qudits, `d >= 5` prime, `s = sin(pi/d)`. `K = c_0 I + sum_j |c_j| u_j` with
`u_j = (c_j/|c_j|) g_j`, where the `g_j` are non-identity Weyl operators with
`g_i g_j = omega^(t_ij) g_j g_i`. `psi` is a top eigenvector, `delta_j = 1 - Re<psi|u_j|psi>`, and
`F = W - lambda_max = sum_j |c_j| delta_j`. Fix `c = c*(d)` from
`qudit-weyl-rounding-one-qudit-constant-is-2d-over-sqrt3-pi-proof`, so that `c > 3` and
`c eta s >= 2/sqrt3` with `eta = 1 - 4/(1+c)`.

Let `T = {j : delta_j < 1/(1+c)}` and `x_j = 1 - c delta_j/(1 - delta_j) in (0, 1]` for `j in T`.
Let `G` be the noncommutation graph on `T`, with `j ~ k` iff `t_jk != 0`.

## Step 1: a random commuting set with Pr(j in I) >= x_j suffices

Let `I` be a commuting subset of `T`. Apply (Q2)–(Q4) of
`qudit-weyl-rounding-constant-linear-upper-bound-proof` with the good set `G` there replaced by `I`.
Measure `{u_k : k in I}` on `psi`, then output a uniform stabilizer state of the joint eigenspace,
extended to a maximal stabilizer group. Let `I*` be the set of `j` with `u_j` in `C^* <u_k : k in I>`,
so `I* ⊇ I`. Then the expected value is exactly `sum_(j in I*) |c_j| (1 - delta_j)`. The reason is
(Q2) `E_mu x_j = <psi|u_j|psi>` for `j in I*`, together with (Q4) `E_nu <phi|u_j|phi> = 0` for
`j not in I*`. Hence

```text
lambda_max - E<phi|K|phi> = sum_(j not in I*) |c_j|(1 - delta_j) <= sum_(j not in I, delta_j < 1) |c_j| (1 - delta_j).
```

Now let `I` be random with `Pr(j in I) >= x_j` for `j in T`. For `j in T`, the expected charge is at
most `|c_j| (1 - delta_j)(1 - x_j) = c |c_j| delta_j`. For `j not in T` with `delta_j < 1`, we have
`delta_j >= 1/(1+c)`, so `1 - delta_j <= c delta_j`. So the expected loss is at most `cF`, and some
outcome attains it.

## Step 2: STAB membership

`STAB(G)`, the convex hull of indicator vectors of independent sets, is down-closed in `[0,1]^T`. So
a random `I` as in Step 1 exists iff `x in STAB(G)`. By separation, that holds iff
`sum_j w_j x_j <= alpha_w(G)` for every `w >= 0` on `T`.

## Step 3: (**) gives the separation inequality

Fix `w >= 0` on `T` and put `D = diag(sqrt w)`. Apply Lemma L (L1)
(`qudit-weyl-rounding-one-qudit-constant-is-2d-over-sqrt3-pi-proof`) to the unitaries `u_j`,
`j in T`: `sum_T w_j delta_j >= ||DCD||_1/4`. Here `C_jk = (1 - omega^(t_jk)) z_jk` vanishes on the
diagonal and on commuting pairs, i.e. on the non-edges of `G`. On edges,
`|C_jk| = 2|sin(pi t_jk/d)| |z_jk| >= 2 s eta`, by (L3) and `delta < 1/(1+c)`. So `C' = C/(2 s eta)`
satisfies the hypotheses of (**), and

```text
sum_T w_j delta_j  >=  (s eta/2) ||D C' D||_1  >=  (sqrt3/2) s eta (W_T - alpha_w(G)),     W_T = sum_T w_j.
```

Since `x_j <= 1 - c delta_j`,

```text
sum_T w_j x_j  <=  W_T - c sum_T w_j delta_j  <=  W_T - (sqrt3/2) c s eta (W_T - alpha_w)  <=  alpha_w ,
```

because `(sqrt3/2) c s eta >= 1` and `W_T >= alpha_w`. By Steps 2 and 1, `c_d <= c*(d)`. QED
(conditional on (**)).

## Remarks

- On one qudit, `G` is complete multipartite, with parts given by lines. Its STAB is cut out by
  the transversal clique constraints. Step 3 then needs (**) only for cliques of pairwise
  noncommuting Weyl operators, and the one-qudit proof supplies it through Frobenius, Lemma T and
  Turán's theorem. For `n >= 2`, a clique can have all `t_jk = +-1`, for example `v_k = (e_k, u_k)`
  with `u_k` the upper-triangular all-ones column. So the Frobenius bound is too weak (see Attempt 1
  of `hermitian-edge-trace-norm-vs-independence`), and odd-cycle and other facets appear.
- In the semiclassical regime `C` is nearly purely imaginary:
  `C_jk = -2i sin(pi t_jk/d) e^(i pi t_jk/d) z_jk`, with `arg z_jk = O(sqrt delta)`. So the purely
  imaginary case of (**), which `graph_relaxed.py` checks, carries the leading order. Controlling the
  phase error would give only `c_d <= 2d/(sqrt3 pi) + O(sqrt d)`, which is not written out here.
