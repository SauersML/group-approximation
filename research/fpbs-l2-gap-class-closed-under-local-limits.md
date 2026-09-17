---
rg: 2
id: fpbs-l2-gap-class-closed-under-local-limits
kind: claim
title: A critical l2 gap with fixed constants survives local limits, and finite or amenable approximants never supply one
distinct_from:
  fpbs-expander-approximant-giant-data-is-glued: that shows giant-component data of finite large-set expander approximants converges to the glued law; this is an operator statement for arbitrary local limits, needs no expansion, and proves the gap class is closed while finite and amenable approximants have no margin above p_c at any fixed operator bound.
  fpbs-l2-gap-gives-bounded-pivotal-counts: that turns a finite connectivity-operator norm on one graph into a pivotal bound; this says when such a norm bound passes from approximating graphs to their local limit.
  fpbs-acylindrically-hyperbolic-critical-l2-gap: that proves p_c<p_(2->2) qualitatively on one class of groups; this shows the gap transplants to limits only with a common norm bound M and a common margin delta, which qualitative theorems do not provide.
  fpbs-nonamenability-bounds-critical-connectivity-operator: that conjectures a critical l2 bound on every nonamenable transitive graph; this proves only closedness of the uniform gap class and an obstruction for finite and amenable approximants.
artifacts:
  - research/artifacts/fpbs-l2-gap-local-limits-2026-09-17.md
---

**ESTABLISHED.** Let `G_k -> G` locally: for each `r` the rooted `r`-balls
eventually agree. Convergence of marked groups is the Cayley-graph case. Let
`T^G_p` be the operator with kernel `tau_p(x,y) = P_p(x <-> y)`, and put
`Gamma_M(G) = sup{p : ||T^G_p||_(2->2) <= M}`.

1. **Lower semicontinuity.** For every `p`,
   `||T^G_p|| <= liminf_k ||T^{G_k}_p||`.
2. **Closed uniform gap class.** Suppose all graphs are infinite and
   transitive, and let `g_M = Gamma_M - p_c`. Then `g_M` is upper
   semicontinuous.
   - Hence `U_(M,delta) = {G : ||T^G_(p_c(G)+delta)|| <= M}` is closed for all
     `M` and all `delta > 0`.
   - `C_2 = {p_c < p_(2->2)}` is the countable union of the `U_(M,1/j)`, so it
     is `F_sigma`.
   - The input is Duminil-Copin–Tassion's finite-set characterisation of
     `p_c`, which makes `p_c` lower semicontinuous.
3. **Transplant criterion.** Suppose `G_k` lies in `U_(M,delta)` for infinitely
   many `k`.
   - Then `p_c(G) < p_c(G)+delta <= p_(2->2)(G) <= p_u(G)`.
   - On Cayley graphs, also `E_p[N_(n,R)|E_(n,R)] <= 2dM^2` for all `n`, all
     `R >= n` and all `p` in `[p_c(G), p_c(G)+delta]`.
4. **Obstruction.** Suppose each `G_k` is finite and transitive, or infinite,
   transitive and amenable. Then `limsup_k Gamma_M(G_k) <= p_c(G)` for every
   `M`.
   - The reason is that on such graphs `||T_p||` is at least the truncated
     susceptibility `chi_r(p)`.
   - `chi_r(p)` is ball-local, and it tends to infinity as `r` grows for every
     `p > p_c(G)`.
   - So every finite-model or amenable-model transplant of the operator gap
     dies at the uniform-margin step.

The proofs are in
`research/artifacts/fpbs-l2-gap-local-limits-2026-09-17.md`:

| Part | Where |
| --- | --- |
| Part 1 | Theorem 2.1 |
| Part 2 | Lemma 1.1 and Theorem 3.1 |
| Part 3 | Corollary 3.2 |
| Part 4 | Proposition 4.1 |

The artifact also records the decomposition. `BS(G)` follows from three
prerequisites, each of which can fail:

* [D1] approximants;
* [D2] one common norm bound `M`;
* [D3] one common margin `delta`.

Finite and amenable approximants fail [D2]. Qualitative gap theorems stop at
[D3].
