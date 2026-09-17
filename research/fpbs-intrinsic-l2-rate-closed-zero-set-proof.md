---
rg: 2
id: fpbs-intrinsic-l2-rate-closed-zero-set-proof
kind: route
title: Split a shortest open path at its R-th vertex with BK, take Fekete infima of continuous functions, and use subcritical finite susceptibility for the zero set
target: fpbs-intrinsic-l2-rate-closed-zero-set
requires: []
---

Complete written proof. No computation is used. Notation as in the claim.

**Standard imports.**

- **BK inequality.** Increasing events `A,B` depending on a finite edge set
  satisfy `P_t(A o B) <= P_t(A) P_t(B)`. Here `A o B` means disjoint
  occurrence. Source: G. Grimmett, *Percolation*, 2nd ed., Springer 1999,
  Section 2.3. It is used the same way in the ESTABLISHED
  `fpbs-bk-majorant-integrated-sensitivity-is-critical-l2-proof`.
- **Sharpness in the Duminil-Copin--Tassion form.** [DT] arXiv:1502.03050v3,
  TeX source `sharpnessPercoIsing-H.tex`, as imported with line numbers in
  `fpbs-l2-gap-class-closed-under-local-limits-proof`. Lines 314--322 define
  `tilde beta_c = sup{beta : varphi_beta(S) < 1 for some finite S containing 0}`
  and state verbatim "This directly implies that $\tilde{\beta_c}=\beta_c$".
  Lines 349--354 give the bond form, with
  `varphi_p(S) = p sum_(x in S) sum_(y notin S, {x,y} in E) P_p[0 <->_S x]`.
  So `p_c = sup{p : varphi_p(S) < 1 for some finite S containing o}`. Here
  `<->_S` means connected by an open path with all vertices in `S`.
- **Fekete's lemma.** If `a_(R+R') <= a_R + a_(R')` and `a_R` is finite for
  `R >= 1`, then `lim_R a_R/R = inf_R a_R/R` in `[-infinity, infinity)`.

Two elementary kernel facts are used throughout. All kernels are nonnegative.

- **(K1)** If `0 <= K <= K'` entrywise, then `||K||_(2->2) <= ||K'||_(2->2)`.
  Indeed `|Kf| <= K|f| <= K'|f|` pointwise.
- **(K2)** If `K(u,v) = f(u^(-1)v)` with `f >= 0` finitely supported, then
  `(Kphi)(u) = sum_h f(h) phi(uh)`. Right translation is unitary on `l2(Gamma)`,
  so `||K||_(2->2) <= ||f||_1`. Also `<delta_o, K delta_o> = f(e)`.

Left multiplication by `Gamma` preserves `G` and the law of `omega_t`. So every
kernel here has the form (K2), with
`f^(R)_t(h) = P_t(d_omega(o,h) <= R)`, supported in `B_R(o)`.

## Step 1. BK submultiplicativity in the intrinsic radius

Fix `u,v` and `R,R' >= 1`. Suppose `d_omega(u,v) <= R+R'` and choose a
shortest open path `gamma = (u = x_0, x_1, ..., x_L = v)`. It is a simple path
with `L <= R+R'`.

- If `L <= R`, then `{d_omega(u,v) <= R}` occurs.
- If `L > R`, put `w = x_R`. The edge sets `{x_(i-1)x_i : i <= R}` and
  `{x_(i-1)x_i : R < i <= L}` are disjoint, and each is an open path, of length
  `R` and `L-R <= R'` respectively. So `{d_omega(u,w) <= R} o {d_omega(w,v) <= R'}`
  occurs.

In both cases, taking `w = v` in the first case,

```text
{d_omega(u,v) <= R+R'}  ⊆  ⋃_(w in B_R(u)) {d_omega(u,w) <= R} o {d_omega(w,v) <= R'},
```

where for `w = v` the second event is the sure event. Every event here is
increasing and depends only on the edges of `B_(R+R')(u)`. By the union bound
and BK,

```text
T^(R+R')_t(u,v) <= sum_w T^(R)_t(u,w) T^(R')_t(w,v) = (T^(R)_t T^(R')_t)(u,v).
```

By (K1), `||T^(R+R')_t|| <= ||T^(R)_t T^(R')_t|| <= ||T^(R)_t|| ||T^(R')_t||`,
so `a_(R+R') <= a_R + a_(R')`. Summing the entrywise inequality over `v` gives
`E|B^int_(R+R')(o)| <= E|B^int_R(o)| E|B^int_(R')(o)|`.

Bounds: `<delta_o, T^(R)_t delta_o> = 1`, so `a_R >= 0`. By (K2),
`||T^(R)_t|| <= ||f^(R)_t||_1 = E_t|B^int_R(o)| <= |B_R|`. Fekete's lemma gives
the existence of both limits as infima, and
`0 <= Lambda(t) <= lambda_1(t) <= lim_R R^(-1) log|B_R| = log gr <= log d`.
This is item 1.

## Step 2. Continuity in `t`, semicontinuity of the rates

For `h in B_R(o)`, the event `{d_omega(o,h) <= R}` depends only on the finitely
many edges of `B_R(o)`. So `f^(R)_t(h)` is a polynomial in `t`. By (K2) and the
triangle inequality,

```text
| ||T^(R)_t|| - ||T^(R)_s|| |  <=  ||f^(R)_t - f^(R)_s||_1 = sum_(h in B_R) |f^(R)_t(h) - f^(R)_s(h)|,
```

a finite sum of continuous functions. So `t -> ||T^(R)_t||` is continuous. It
is at least `1`, so `a_R` is continuous. The same holds for
`log E_t|B^int_R(o)| = log sum_h f^(R)_t(h)`, since the sum is at least `1`.

In the monotone coupling `omega_s ⊆ omega_t` for `s <= t`, so `d_omega` is
nonincreasing in `t`, `f^(R)_t` is entrywise nondecreasing, and by (K1) `a_R` is
nondecreasing.

By Step 1, `Lambda = inf_R a_R/R` is an infimum of continuous nondecreasing
functions. It is therefore nondecreasing and upper semicontinuous. A
nondecreasing upper semicontinuous function is right-continuous: if
`t_n ↓ t`, then `Lambda(t) <= Lambda(t_n)` and
`limsup Lambda(t_n) <= Lambda(t)`. Since `Lambda >= 0`, its zero set is
`{Lambda <= 0}`. That set is closed by upper semicontinuity and is an initial
interval by monotonicity, so it equals `[0,p_Lambda]`. The same argument
applies verbatim to `lambda_1`. This is item 2.

## Step 3. Subcritical finite susceptibility and the zero set

**Lemma 3.1.** If `S` is finite with `o in S` and `varphi_t(S) < 1`, then
`chi(t) = E_t|C_o| <= |S|/(1 - varphi_t(S))`.

*Proof.* Let `H_n` be the subgraph induced on `B_n(o)`, `C_z(H_n)` the open
cluster of `z` in `omega_t ∩ E(H_n)`, and `M_n = max_(z in B_n) E_t|C_z(H_n)|`,
which is finite. Fix `z in B_n`, put `S_z = zS`, and let `x in B_n \ S_z` with
`z <-> x` in `H_n`. Along an open path in `H_n` from `z` to `x`, let `y'` be the
first vertex outside `S_z` and `y` its predecessor. The initial segment, the
edge `yy'` and the final segment are edge-disjoint open witnesses. So
`{z <->_(S_z) y in H_n} o {yy' open} o {y' <-> x in H_n}` occurs. These are
increasing events on the finite edge set `E(H_n)`. Applying BK twice, then
summing over `x`, and bounding the contribution of `x in S_z` by `|S|`,

```text
E_t|C_z(H_n)| <= |S| + sum_(y in S_z, y' notin S_z, yy' in E(H_n)) t P_t(z <->_(S_z) y) E_t|C_(y')(H_n)|
             <= |S| + varphi_t(S) M_n.
```

Here `P_t(z <->_(S_z) y in H_n) <= P_t(o <->_S z^(-1)y)` by monotonicity in the
edge set and invariance, and `y' in B_n`. Taking the maximum over `z` gives
`M_n <= |S| + varphi_t(S) M_n`, so `M_n <= |S|/(1-varphi_t(S))`. Finally
`E_t|C_o(H_n)|` increases to `E_t|C_o|` by monotone convergence. QED.

**Zero set.** Let `t < p_c`. By [DT] there are `p > t` and a finite `S`
containing `o` with `varphi_p(S) < 1`. The map `p -> p P_p(o <->_S x)` is
nondecreasing, so `varphi_t(S) <= varphi_p(S) < 1`, and by Lemma 3.1
`chi(t) < infinity`. For every `R`,
`E_t|B^int_R(o)| <= chi(t)`, so `lambda_1(t) = 0`. Hence
`[0,p_c) ⊆ {lambda_1 = 0}`, and this set is closed by Step 2, so
`lambda_1(p_c) = 0`. Since `0 <= Lambda <= lambda_1`, also `Lambda = 0` on
`[0,p_c]`, and `p_c <= p_lambda1 <= p_Lambda`. Right-continuity at `p_c` gives
`lambda_1(t), Lambda(t) -> 0` as `t ↓ p_c`.

If `||T_t|| < infinity`, then `T^(R)_t <= T_t` entrywise, so `a_R(t)` is bounded
by (K1) and `Lambda(t) = 0`. So `[0,p_(2->2)) ⊆ {Lambda = 0}`, and closedness
gives `p_(2->2) <= p_Lambda`. This is item 3.

## Step 4. Linear stretch forces a positive rate

Let `K` be a linear stretch constant at `t`, with
`c = inf_(u,v) P_t(d_omega(u,v) <= K(d(u,v)+1)) > 0`. For `m >= 0` put
`R_m = ceil(K(2m+1))`. Any `u,v in B_m(o)` satisfy `d(u,v) <= 2m`, so
`T^(R_m)_t(u,v) >= c`. Testing against `phi = 1_(B_m)`,

```text
||T^(R_m)_t|| >= <phi, T^(R_m)_t phi>/||phi||^2 >= c |B_m|^2/|B_m| = c |B_m|.
```

Since the limit `Lambda(t) = lim_R a_R/R` exists (Step 1), it equals the limit
along `R_m`:
`Lambda(t) >= lim_m (log c + log|B_m|)/ceil(K(2m+1)) = log(gr)/(2K)`.

If `s <= t` and `K` is a linear stretch constant at `s`, then it is one at `t`,
because `d_(omega_t) <= d_(omega_s)` in the coupling. So `K_*` is
nonincreasing. This is item 4.

## Step 5. The contradiction lemma

Suppose `q < 1` and `Lambda >= delta > 0` on `(q,q+epsilon)`. Right-continuity
(Step 2) gives `Lambda(q) = lim_(t↓q) Lambda(t) >= delta`. So `q` is not in the
zero set `[0,p_Lambda]`, that is `q > p_Lambda`, and `p_Lambda >= p_c` by
Step 3. The argument for `lambda_1` is the same, using its right-continuity and
`p_lambda1 >= p_c`. The equivalence with `E_q|B^int_R(o)| >= e^(delta R)` for
all `R` is the infimum form of Fekete's lemma (Step 1). This is item 5.

## Step 6. Stretch diverges at `p_c+`

If `K` is a linear stretch constant at `t`, Steps 1 and 4 give
`log(gr)/(2K) <= Lambda(t) <= lambda_1(t)`. So `lambda_1(t) > 0`, because
`gr > 1` by nonamenability, and `K >= log(gr)/(2 lambda_1(t))`. If
`lambda_1(t) = 0` there is no stretch constant and `K_*(t) = +infinity`.
Since `lambda_1(t) -> 0` as `t ↓ p_c` (Step 3), `K_*(t) -> infinity`. This is
item 6. QED.
