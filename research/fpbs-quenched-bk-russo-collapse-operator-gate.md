---
rg: 2
id: fpbs-quenched-bk-russo-collapse-operator-gate
kind: claim
title: Collapse families that are quenched Bernoulli products with exact annealed sprinkling exist over sparse spines, so the only product-structure input left is the annealed operator Russo-BK inequality with summable jump kernels
distinct_from:
  fpbs-sharp-dominating-collapse-over-sparse-spines: same family; that node lists the surviving inputs as BK, Russo or independent sprinkling at unbounded range, while this proves quenched Harris-FKG, BK-Reimer and Russo for every environment, the annealed Russo formula off the jump times and exact annealed independent sprinkling, and proves that the only failing product input is an annealed operator inequality (G) that it isolates and integrates
  fpbs-fiid-uniform-finite-energy-fkg-collapse-family: that proves FIID, uniform finite energy and annealed FKG and says BK and Russo fail for the annealed law; this shows they hold conditionally on the invariant environment and locates the defect in annealing operator kernels, not in the edge-level tools
  fpbs-bk-majorant-integrated-sensitivity-is-critical-l2: that integrates the Bernoulli Russo-BK inequality for walk connectivity; this integrates an abstract annealed inequality with jump atoms for an arbitrary monotone family and shows a collapse family must violate it
  fpbs-critical-l2-implies-nonuniqueness: that is Hutchcroft's Bernoulli criterion; Theorem 2 here is its abstract form for monotone families with jumps, used as a gate that every collapse family must fail
---

**ESTABLISHED (class-killing obstruction).** Proof in
`fpbs-quenched-bk-russo-collapse-operator-gate-proof`.

**Setting.** `Gamma` is nonamenable and finitely generated, `S` is a finite
symmetric generating set with `|S| = d`, and `G = Cay(Gamma,S)`. `J` is the
adjacency matrix. `xi_t = {e : U_e <= t}` is the standard coupling. For a
monotone family `(omega_t)` and a finite edge set `Lambda`, put
`T^Lambda_t(u,v) = P(u <-> v in omega_t ∩ Lambda)` with `T^Lambda_t(u,u) = 1`,
and `T_t(u,v) = P(u <-> v in omega_t)`. Norms are `l2(V) -> l2(V)`.

Let `(omega_t)` be the family of `fpbs-sharp-dominating-collapse-over-sparse-spines`,
with arbitrary `f` and `R`:

```text
omega_t = xi_t                (t <= p_c),
omega_t = xi_t ∪ A_{n(t)}     (t >  p_c),
```

where `A_1 ⊇ A_2 ⊇ ...` are connected invariant random subgraphs, independent
of `U`, and `n` is nonincreasing and integer-valued. Let `M = sigma(A_n : n >= 1)`
be the environment. The jump set `D` of `n` is finite on every
`[p_c+eta, 1]`.

**Theorem 1 (quenched product structure).**

* **(Q1) Quenched product law.** Given `M`, the processes
  `(omega_t(e))_{t in [0,1]}`, `e in E`, are independent, with
  `omega_t(e) = 1{U_e <= p_e(t)}`. Here `p_e(t) = 1` if `t > p_c` and
  `e in A_{n(t)}`, and `p_e(t) = t` otherwise. So for every realisation of the
  environment and every `t`, the quenched law is a product measure. It
  satisfies Harris-FKG and BK-Reimer, and it dominates `P_t`.
* **(Q2) Russo off jumps.** Let `I` be an open interval on which `n = k` is
  constant, and let `E` be an increasing event determined by finitely many
  edges. Then
  for `t in I`:
  `d/dt P^M(omega_t in E) = sum_{e notin A_k} P^M(e pivotal for E in omega_t)`.
  Also `d/dt P(omega_t in E) = sum_e P(e notin A_k, e pivotal for E in omega_t)`,
  and quenched `d/dt tau^{M,Lambda}_t <= tau^{M,Lambda}_t J tau^{M,Lambda}_t`
  entrywise.
* **(Q3) Quenched block jumps.** Let `r in D`, `k = n(r-)`, `k' = n(r+)` and
  `F = A_{k'} \ A_k`. Let `omega_-` and `omega_+` be the configurations just
  before and just after `r`, with the same `xi_r`. Then
  `tau^{M,Lambda}_+(u,v) - tau^{M,Lambda}_-(u,v) <= sum_{a,b in V(F)} tau^{M,Lambda}_-(u,a) tau^{M,Lambda}_-(b,v)`.
  The jump kernel is the all-pairs kernel `1_{V(F)} 1_{V(F)}^T`. By the
  mass-transport principle `F` is a.s. infinite on `{F ≠ ∅}`, and there the
  kernel has infinite operator norm.
* **(Q4) Exact annealed independent sprinkling.** For `0 <= t < t' <= 1`, on
  an extension by independent uniforms there is a Bernoulli`((t'-t)/(1-t))`
  edge configuration `S`. It is independent of `(M, (omega_s)_{s <= t})` and
  satisfies `omega_t ∪ S ⊆ omega_{t'}`.
* **(Q5) Local annealed BK.** Let `t in (p_c,t_1]`, and let `E` and `F` be
  events determined by the edges of one ball of radius `R(t)`. Then
  `P(E∘F) <= P(E)P(F) + 4f(t)`, and `P(E∘F) <= P(E)P(F) + f(t)` if `E` and `F`
  are increasing.

**Theorem 2 (operator gate).** Let `G` be a graph of maximal degree `d` (with
multiplicity), and let `(omega_t)_{t in [t_0,t_0+eps]}` be a monotone family of
random edge sets. Suppose there are:

* a nonnegative `C in L^1([t_0,t_0+eps])`;
* points `r_k in (t_0,t_0+eps]` and weights `m_k >= 0` with `sum m_k < infinity`,

such that for every finite `Lambda` and all `t_0 <= s < t <= t_0+eps`,
entrywise

```text
(G)  T^Lambda_t - T^Lambda_s <= ∫_s^t C(r) T^Lambda_r J T^Lambda_r dr
                                + sum_{s < r_k <= t} m_k T^Lambda_{r_k-} J T^Lambda_{r_k-} .
```

Put `kappa(t) = ∫_{t_0}^t C + sum_{r_k <= t} m_k`. If `||T_{t_0}|| < infinity`
and `d ||T_{t_0}|| kappa(t) < 1`, then
`||T_t|| <= ||T_{t_0}|| / (1 - d ||T_{t_0}|| kappa(t))`. In particular, if
`G` is infinite, then `inf_{u,v} T_t(u,v) = 0`, so `omega_t` is not
FKG-unique: it cannot satisfy `T_t >= theta(t)^2 > 0`.

**Corollary 3 (obstruction).** Let `G` have invariant sparse spines and
`||T_{p_c}||_{2->2} < infinity`. Closed hyperbolic mapping tori of
pseudo-Anosov surface maps are examples, by Corollary C of
`fpbs-soft-collapse-iff-invariant-sparse-spines` and Hutchcroft's hyperbolic
L2 theorem. Then the family above satisfies (Q1)-(Q5) and (H1)-(H5) of the
sharp dominating family, and it has `T^omega_{p_c} = T_{p_c}`. Yet for every
`eps > 0`, every integrable `C` and every summable `(r_k, m_k)`, its annealed
kernels violate (G) on `[p_c, p_c+eps]`. Equivalently, at least one of the
following annealing estimates fails near `p_c`, uniformly in `Lambda`:

* **(a) interval factorization:**
  `E[tau^M J tau^M] <= C(r) T J T` with `C` integrable;
* **(b) jump factorization:**
  `E[tau^M_- 1_{V(F)} 1_{V(F)}^T tau^M_-] <= m_k T_- J T_-` with
  `sum m_k < infinity`.

Every environment realisation satisfies (G) on each jump-free interval with
`C = 1`.

**Class killed.** No argument proves `p_c < p_u` on these graphs if, above
`p_c`, it uses only the inputs of the sharp dominating corollary together with
any of the following:

* Harris-FKG, BK-Reimer or the Russo formula applied conditionally on an
  invariant environment independent of the labels;
* the annealed Russo formula at all but countably many parameters;
* independent sprinkling, including sprinkling between distant regions and
  uniqueness-monotonicity arguments built on it;
* BK at bounded range `R(t)`.

This removes "BK, Russo or independent sprinkling" from the survivors list
of `fpbs-sharp-dominating-collapse-over-sparse-spines`. The surviving product
input is (G) itself, an annealed operator-norm Russo-BK inequality whose jump
kernels have summable operator weight. Theorem 2 shows that (G), together
with `||T_{p_c}|| < infinity`, already gives the window. So this step is the
exact gate.

**Exact failing step.** A proof transcribes edge-level product tools into
the annealed two-point operator. The quenched diagram `tau^M J tau^M` and the
quenched jump kernel must average to a bounded multiple of `T J T` uniformly
in the volume, and they do not. Whether (a) or (b) is the load-bearing
failure is not decided here.
