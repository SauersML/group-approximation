---
rg: 2
id: fpbs-quenched-bk-russo-collapse-operator-gate-proof
kind: route
title: Condition the sharp dominating collapse family on its spine environment to get product measures, sprinkle from the labels, integrate an abstract Russo-BK operator inequality with atoms, and play the two against a critical L2 graph
target: fpbs-quenched-bk-russo-collapse-operator-gate
requires:
  - fpbs-sharp-dominating-collapse-over-sparse-spines
  - fpbs-soft-collapse-iff-invariant-sparse-spines
---

Notation as in the target. `P^M` is the conditional law given the environment
`M = sigma(A_n : n >= 1)`. For a finite edge set `Lambda`,
`tau^{M,Lambda}_t(u,v) = P^M(u <-> v in omega_t ∩ Lambda)`, so
`T^Lambda_t = E[tau^{M,Lambda}_t]`. `t_1 = (1+p_c)/2`. Facts about the family
are quoted from `fpbs-sharp-dominating-collapse-over-sparse-spines-proof`
(Steps 2-6) and its target (H1-H5):

* `A_n` is a function of auxiliary variables independent of `U`.
* `P(o in V(A_n)) <= 3 · 2^-n`.
* `|B_{R(t)}| · 3 · 2^-n(t) <= f(t)` for `t in (p_c,t_1]` (display (3.1)).
* `T^omega_t(u,v) >= theta_xi(t)^2` for all `u,v` and `t > p_c` (H5).

## 1. (Q1) Quenched product law

`n` is deterministic and `M` is independent of `U`. For every edge `e`,

```text
omega_t(e) = 1{U_e <= t} ∨ 1{t > p_c, e in A_{n(t)}} = 1{U_e <= p_e(t)},
```

with `p_e(t) = 1` if `t > p_c` and `e in A_{n(t)}`, and `p_e(t) = t`
otherwise. The function `t -> p_e(t)` is `M`-measurable. Given `M`, the labels
`U_e` are still iid uniform, so the processes `(omega_t(e))_t` are
conditionally independent over `e`. Hence for each `t` the quenched law of
`omega_t` is the product measure with densities `p_e(t) in {t,1}`. Product
measures with arbitrary densities satisfy Harris-FKG (Harris) and BK-Reimer
(van den Berg-Kesten for increasing events, Reimer in general). Since
`p_e(t) >= t`, the quenched law dominates `P_t`. ∎

## 2. (Q2) Russo off jumps

Let `I` be an open interval with `n = k` on `I`, and let `E` be increasing and
determined by a finite edge set `F_E`. For `t in I`, `p_e(t) = t` for
`e notin A_k` and `p_e(t) = 1` for `e in A_k`. So `P^M(omega_t in E)` is a
multilinear polynomial in `(p_e)_{e in F_E}` evaluated along `p_e(t)`. For
product measures and increasing `E`,
`∂P/∂p_e = P(omega^{e,1} in E) - P(omega^{e,0} in E) = P(e pivotal for E)`,
where `omega^{e,i}` sets `e` to `i`. The pivotal event does not depend on
`omega(e)`. The chain rule then gives

```text
d/dt P^M(omega_t in E) = sum_{e in F_E \ A_k} P^M(e pivotal for E in omega_t).
```

The right side is at most `|F_E|`. By dominated convergence we may
differentiate `P(omega_t in E) = E[P^M(omega_t in E)]` under `E`. Since
`1{e notin A_k}` is `M`-measurable,
`d/dt P(omega_t in E) = sum_e P(e notin A_k, e pivotal for E in omega_t)`.

**Two-point bound.** Take `E = {u <-> v in omega ∩ Lambda}`, with
`F_E = Lambda`. Suppose `e = {a,b} in Lambda` is pivotal. Then
`omega^{e,1} ∩ Lambda` contains a self-avoiding path `gamma` from `u` to `v`
that uses `e`. Orient `e` along `gamma` and write it as `(a,b)`. The subpaths
`gamma[u,a]` and `gamma[b,v]` are edge-disjoint, avoid `e`, and lie in
`omega ∩ Lambda`. So `{u <-> a in omega ∩ Lambda} ∘ {b <-> v in omega ∩ Lambda}`
occurs for one of the two orientations. By quenched BK,

```text
P^M(e pivotal) <= tau^{M,Lambda}(u,a) tau^{M,Lambda}(b,v) + tau^{M,Lambda}(u,b) tau^{M,Lambda}(a,v).
```

Summing over `e in Lambda \ A_k`, with each edge counted once in each
orientation, gives
`d/dt tau^{M,Lambda}_t(u,v) <= (tau^{M,Lambda}_t J tau^{M,Lambda}_t)(u,v)`.
Integrating over a jump-free interval `[s,t] ⊆ I` gives the quenched form of
(G) with `C = 1` and no atoms. ∎

## 3. (Q3) Quenched block jumps

Let `r in D`, `k = n(r-)`, `k' = n(r+) < k`, `omega_- = xi_r ∪ A_k`,
`omega_+ = xi_r ∪ A_{k'}` and `F = A_{k'} \ A_k`. Since `P(U_e = r) = 0`,
`T^Lambda_{r-} = E[tau^{M,Lambda}_-]` and `T^Lambda_{r+} = E[tau^{M,Lambda}_+]`,
where `tau_±` are computed in `omega_±`.

Because `omega_- ⊆ omega_+`,
`tau_+(u,v) - tau_-(u,v) = P^M(u <-> v in omega_+ ∩ Lambda, not in omega_- ∩ Lambda)`.
On that event take a self-avoiding path `gamma` in `omega_+ ∩ Lambda` from `u`
to `v`. It uses an edge of `F`, since otherwise all its edges lie in
`omega_+ \ F ⊆ xi_r ∪ A_k = omega_-`. Let `e_1` and `e_2` be the first and last
`F`-edges on `gamma`. Let `a` be the endpoint of `e_1` that `gamma` visits
first, and `b` the endpoint of `e_2` that it visits last. Then `gamma[u,a]`
and `gamma[b,v]` contain no `F`-edge, so they lie in `omega_- ∩ Lambda`. They
are edge-disjoint because `gamma[u,a]` precedes `e_1` and `gamma[b,v]` follows
`e_2`. So `{u <-> a} ∘ {b <-> v}` occurs in `omega_- ∩ Lambda` with
`a, b in V(F)`. A union bound and quenched BK (Q1, for `omega_-`) give

```text
tau^{M,Lambda}_+(u,v) - tau^{M,Lambda}_-(u,v) <= sum_{a,b in V(F)} tau^{M,Lambda}_-(u,a) tau^{M,Lambda}_-(b,v).
```

**`F` is infinite or empty.** The set `F` is an invariant random subgraph. On
`{0 < |V(F)| < infinity}`, send mass `1/|V(F)|` from every vertex `x` to every
`y in V(F)`. The expected mass sent from `o` is at most `1`. The mass received
at `o` is infinite on `{o in V(F), 0 < |V(F)| < infinity}`. By the MTP that
event is null, and by invariance and a countable union so is
`{0 < |V(F)| < infinity}`. On `{F ≠ ∅}` the kernel `1_{V(F)} 1_{V(F)}^T` has
infinite operator norm. ∎

## 4. (Q4) Exact annealed independent sprinkling

Let `(V_e)` be iid uniforms, independent of everything, and
`s = (t'-t)/(1-t)`. Put `S_e = 1{t < U_e <= t'}` if `U_e > t`, and
`S_e = 1{V_e <= s}` if `U_e <= t`. Let
`G_t = sigma(M, U_e 1{U_e <= t}, 1{U_e <= t} : e in E)`. It contains
`sigma(M, (omega_s)_{s <= t})`, because `omega_s` for `s <= t` is a function of
`M` and the truncated labels.

`S_e` is a function of `(U_e,V_e)`. These pairs are independent over `e` and
independent of `M`. Given `U_e <= t` and the value of `U_e`, `S_e` is
Bernoulli`(s)` through `V_e`. Given `U_e > t`, `U_e` is uniform on `(t,1]`, so
`P(U_e <= t') = s`. Hence the conditional law of `S_e` given `G_t` is
Bernoulli`(s)`, and `S` is Bernoulli`(s)^E`, independent of `G_t`.

**Inclusion.** Suppose `S_e = 1`. If `U_e > t` then `U_e <= t'`, so
`e in xi_{t'} ⊆ omega_{t'}`. If `U_e <= t` then `e in xi_t ⊆ omega_{t'}`. Also
`omega_t ⊆ omega_{t'}`. So `omega_t ∪ S ⊆ omega_{t'}`.

`S` is an equivariant factor of `(U,V)`, so the extension is still an invariant
system. ∎

## 5. (Q5) Local annealed BK

Fix `t in (p_c,t_1]`, a ball `B` of radius `R(t)` and events `E,F` determined
by `E(B)`. Let `D = {V(A_{n(t)}) ∩ B ≠ ∅}`. It is `M`-measurable, and by
invariance
`P(D) <= |B_{R(t)}| · 3 · 2^-n(t) <= f(t)`. Put `X = P^M(E)`, `Y = P^M(F)`,
`x = P_t(E)` and `y = P_t(F)`. On `D^c` no edge of `E(B)` lies in `A_{n(t)}`,
so the quenched law on `E(B)` is `P_t`, and `X = x`, `Y = y`. Quenched Reimer
gives `P^M(E∘F) <= XY`. Hence

```text
P(E∘F) = E[P^M(E∘F)] <= E[XY] <= xy + P(D) <= xy + f(t).
```

**General events.** `|P(E) - x| = |E[(X-x) 1_D]| <= f(t)`, and similarly for
`F`. So `xy <= (P(E)+f)(P(F)+f) <= P(E)P(F) + 3f` for `f <= 1`, and
`P(E∘F) <= P(E)P(F) + 4f(t)`.

**Increasing events.** `X >= x` by (Q1) domination, so `P(E) >= x` and
`P(F) >= y`. Then `xy <= P(E)P(F)` and `P(E∘F) <= P(E)P(F) + f(t)`. ∎

## 6. Theorem 2 (operator gate)

**Step 6.1 (finite-volume matrices).** Fix a finite `Lambda` and let
`W = V(Lambda)`. If `u ≠ v` and not both lie in `W`, then
`T^Lambda_t(u,v) = 0`. So `T^Lambda_t = I_{V \ W} ⊕ X_t`, where `X_t` is a
nonnegative `W × W` matrix with unit diagonal. Put `g(t) = ||X_t||`. Then
`||T^Lambda_t|| = g(t) >= 1`.

For nonnegative matrices `0 <= X <= Y` entrywise,
`||X|| = sup{<f,Xh> : f,h >= 0, |f| = |h| = 1} <= ||Y||`, because
`|<f,Xh>| <= <|f|,X|h|>`. The entries of `X_t` are nondecreasing in `t`, so
`g` is nondecreasing and Borel. Left limits `X_{r-}` exist entrywise, and
`g(r-) = ||X_{r-}||` by continuity of the norm on `W × W` matrices. Also
`g(t_0) <= ||T_{t_0}||`, since `X_{t_0}` is entrywise below the compression of
`T_{t_0}` to `W`.

**Step 6.2 (norm inequality).** For `u,v in W`, `T^Lambda(u,a) ≠ 0` forces
`a in W`. So `(T^Lambda J T^Lambda)(u,v) = (X J_W X)(u,v)`, with `J_W` the
restriction of `J` and `||J_W|| <= d`. By (G), `0 <= X_t - X_s` is entrywise at
most `∫_s^t C(r) X_r J_W X_r dr + sum_{s<r_k<=t} m_k X_{r_k-} J_W X_{r_k-}`.
For `f,h >= 0`,
`<f, ∫ C X_r J_W X_r h dr> = ∫ C <f, X_r J_W X_r h> dr <= d |f||h| ∫ C g(r)^2 dr`.
With the triangle inequality this gives, for `t_0 <= s < t`,

```text
(N)  g(t) - g(s) <= d ∫_s^t C(r) g(r)^2 dr + d sum_{s<r_k<=t} m_k g(r_k-)^2 .
```

Write `kappa((s,t]) = ∫_s^t C + sum_{s<r_k<=t} m_k`, after merging atoms at
equal points.

**Step 6.3 (Bihari inequality with atoms).** We claim

```text
1/g(s) - 1/g(t) <= d kappa((s,t])      (t_0 <= s < t <= t_0+eps).
```

Fix `eta in (0,1)`. Choose a finite set `K` of atom points in `(s,t]` whose
remaining atoms in `(s,t]` have total mass `< eta`. Let `c(x) = ∫_{t_0}^x C`,
which is continuous. Choose a partition `s = x_0 < ... < x_N = t` such that:

1. every point of `K` is a partition point;
2. `c(x_{i+1}) - c(x_i) < eta` for all `i`;
3. if `x_j in K`, then `g(x_j-) <= (1+eta) g(x_{j-1})`.

Condition 3 is achieved by taking `x_{j-1}` close enough to `x_j` from the
left, using `g(x) -> g(x_j-)` and `g >= 1`. Refining the partition preserves
all three conditions.

Write `g_i = g(x_i)`. Let `eps_i = c(x_{i+1}) - c(x_i)` plus the mass of non-`K`
atoms in `(x_i,x_{i+1}]`, so `eps_i < 2 eta`. Let `mu_i` be the `K`-mass at
`x_{i+1}`; no `K`-atom lies strictly inside `(x_i,x_{i+1})`. On `(x_i,x_{i+1}]`,
(N) gives `g_{i+1} - g_i <= d eps_i g_{i+1}^2 + d mu_i g(x_{i+1}-)^2`, since
`g(r), g(r-) <= g_{i+1}` there. Dividing by `g_i g_{i+1}` and using
`g(x_{i+1}-) <= g_{i+1}` and condition 3:

```text
1/g_i - 1/g_{i+1} <= d eps_i g_{i+1}/g_i + d (1+eta) mu_i
                  <= d eps_i + 2 d eta (g_{i+1} - g_i) + d (1+eta) mu_i ,
```

where the second line uses `g_{i+1}/g_i = 1 + (g_{i+1}-g_i)/g_i` and `g_i >= 1`.
Summing over `i`:
`1/g(s) - 1/g(t) <= d (1+eta) kappa((s,t]) + 2 d eta g(t)`. Here `g(t)` is
finite (at most `|W|` times the maximal row count), so letting `eta -> 0`
proves the claim.

**Step 6.4 (uniform bound).** With `s = t_0`,
`1/g(t) >= 1/||T_{t_0}|| - d kappa(t)`. When `d ||T_{t_0}|| kappa(t) < 1` this
gives `||T^Lambda_t|| <= K(t) := ||T_{t_0}|| / (1 - d ||T_{t_0}|| kappa(t))`,
uniformly in `Lambda`.

**Step 6.5 (exhaustion).** Let `Lambda_j` increase to `E`. An open path is
finite, so `{u <-> v in omega_t} = ∪_j {u <-> v in omega_t ∩ Lambda_j}`, an
increasing union, and `T^{Lambda_j}_t(u,v)` increases to `T_t(u,v)`. For
finitely supported `f,h >= 0`, monotone convergence gives
`<f,T_t h> = lim_j <f,T^{Lambda_j}_t h> <= K(t) |f||h|`. So `||T_t|| <= K(t)`.

If `T_t(u,v) >= c > 0` for all `u,v`, then for finite `F ⊆ V`,
`<1_F, T_t 1_F> >= c|F|^2`, so `||T_t|| >= c|F|`. That is unbounded on an
infinite graph, a contradiction. Hence `inf_{u,v} T_t(u,v) = 0`. ∎

## 7. Corollary 3

Let `G` have invariant sparse spines and `||T_{p_c}|| < infinity`. Closed
hyperbolic mapping tori of pseudo-Anosov maps qualify:

* the fibration gives a surjection to `Z` with finitely generated kernel, so
  spines exist by Theorem B of `fpbs-soft-collapse-iff-invariant-sparse-spines`;
* the group is hyperbolic (Thurston), so Hutchcroft's hyperbolic theorem gives
  `p_c < p_{2->2}` and hence `||T_{p_c}|| < infinity`, as recorded in Corollary
  C there.

**Step 7.1 (the family violates (G)).** The family satisfies (Q1)-(Q5) by
Sections 1-5, and (H1)-(H5). Also `omega_{p_c} = xi_{p_c}`, so
`T^omega_{p_c} = T_{p_c}`. Suppose (G) held on `[p_c,p_c+eps]` with integrable
`C` and summable `(r_k,m_k)`, `r_k > p_c`. Then `kappa(t) -> 0` as `t ↓ p_c`,
because `∫_{p_c}^t C -> 0` and `sum_{r_k <= t} m_k -> 0` by dominated
convergence. Choose `t in (p_c,p_c+eps]` with `d ||T_{p_c}|| kappa(t) < 1`.
Theorem 2 gives `inf_{u,v} T^omega_t(u,v) = 0`. But (H5) gives
`T^omega_t >= theta_xi(t)^2 > 0`, since `theta_xi(t) > 0` for `t > p_c`. This
is a contradiction.

**Step 7.2 (the dichotomy (a)/(b)).** State (a) and (b) for every finite
`Lambda`:

* **(a)** `E[tau^{M,Lambda}_r J tau^{M,Lambda}_r] <= C(r) T^Lambda_r J T^Lambda_r`
  for a.e. `r in (p_c,p_c+eps]`, with `C` integrable;
* **(b)** at each jump `r_k in D ∩ (p_c,p_c+eps]`,
  `E[tau^{M,Lambda}_- 1_{V(F_k)} 1_{V(F_k)}^T tau^{M,Lambda}_-] <= m_k T^Lambda_{r_k-} J T^Lambda_{r_k-}`,
  with `sum m_k < infinity`.

Suppose both hold. Fix `p_c < s < t <= p_c+eps`. The interval `(s,t]` contains
finitely many jumps. Between jumps, `tau^{M,Lambda}_r` is a polynomial in `r`.
By (Q2) and (Q3), `tau^{M,Lambda}_t - tau^{M,Lambda}_s` is entrywise at most
`∫_s^t tau J tau dr` plus the sum over jumps of the quenched jump kernels.
Taking expectations and applying (a) and (b) gives (G) on `[s,t]`.

Now let `s ↓ p_c`. Almost surely `A_n ∩ Lambda = ∅` for large `n`, since
`P(o in ∩_n V(A_n)) = 0` and `Lambda` is finite. Also `xi_s ∩ Lambda` equals
`xi_{p_c} ∩ Lambda` for `s` close to `p_c`. So `T^Lambda_s -> T^Lambda_{p_c}`
by bounded convergence, and the right side of (G) increases to its value on
`(p_c,t]`. So (G) holds on `[p_c,p_c+eps]`, contradicting Step 7.1. Hence (a)
or (b) fails.

Quenched, each environment satisfies (G) with `C = 1` on jump-free intervals,
by Section 2. ∎

## 8. Remarks and scope

* **What is proved about which estimate fails.** Only the disjunction
  "(a) or (b) fails". In infinite volume the crude bound
  `E[tau^M(u,a) tau^M(b,v)] <= T(u,a) <= theta_xi(r)^-2 T(u,a) T(b,v)` holds by
  (H5). Its constant `theta_xi(r)^-2` is not integrable near `p_c` whenever
  `theta_xi(r) = O(r-p_c)`, and the bound uses (H5), which fails in finite
  volume. So it decides nothing either way.
* **Why the construction jumps.** The environment of this construction
  activates a whole spine level `A_{n-1} \ A_n` at one deterministic
  parameter. The quenched jump kernel is then the all-pairs kernel on an
  infinite set. We do not claim that every collapse family must have such
  jumps. A collapse family with an edge-wise continuous activation schedule
  and bounded annealed jump weights would pin the failure on (a).
* **Other families of the same shape.** The proofs of Sections 1-4 use only
  that `omega_t = xi_t ∪ Z_t`, with `Z_t` increasing, piecewise constant in `t`,
  and independent of `U`. So they apply verbatim to every collapse family of
  that shape.
* **Consequence for the goal.** In the survivors list of
  `fpbs-sharp-dominating-collapse-over-sparse-spines`, BK, Russo and independent
  sprinkling are now realised by a collapse family: quenched, off jumps, and
  exactly annealed, respectively. The surviving product input is the annealed
  operator inequality (G). For Bernoulli percolation (G) holds trivially with
  `C = 1` and no atoms, so this route to `p_c < p_u` still needs
  `||T_{p_c}|| < infinity` (Hutchcroft's critical L2 conjecture) or a weaker
  norm that (G) can be integrated from.
