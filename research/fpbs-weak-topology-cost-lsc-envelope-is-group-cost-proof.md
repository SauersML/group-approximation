---
rg: 2
id: fpbs-weak-topology-cost-lsc-envelope-is-group-cost-proof
kind: route
title: Approximate every free action by conjugates of the maximum action, which all have cost C(Γ)
target: fpbs-weak-topology-cost-lsc-envelope-is-group-cost
requires:
  - burton-kechris-cost-usc-and-maximum-action
  - cost-is-constant-on-weak-equivalence-classes
---

Fix a maximum a_∞ = a_∞,Γ in A(Γ,X,μ). FR is nonempty and upward closed under ≼ (import,
item 3), so a_∞ is free. The imported Theorem 7.1 display gives C(s) ≥ C(a) ≥ C(a_∞) = C(Γ)
for every a ∈ FR. Cost depends only on the orbit relation, so every conjugate of a_∞ is free
with cost C(Γ). The conjugacy class K of a_∞ is dense in A(Γ,X,μ) (import, item 2), hence
dense in FR.

**Items 1 and 2.**
- Upper bound: every weak neighbourhood U of b ∈ FR meets K, so
  inf{C(c) : c ∈ U ∩ FR} ≤ C(Γ).
- Lower bound: C ≥ C(Γ) on FR.

So the envelope equals C(Γ). Cost is lower semicontinuous at b exactly when C(b) is at most its
envelope, that is, when C(b) ≤ C(Γ). With C(b) ≥ C(Γ) this means C(b) = C(Γ).

**Item 3.**
- If Γ has fixed price, cost is constant on FR, hence continuous.
- Continuity on FR implies lower semicontinuity at s.
- If cost is lower semicontinuous at s, then item 2 gives C(s) = C(Γ). For every a ∈ FR the
  display then gives C(Γ) ≤ C(a) ≤ C(s) = C(Γ), which is fixed price.

**Item 4.** Pick c_n ∈ K with c_n → b; this is possible since K is dense. Then
Ψ(b) ≤ liminf Ψ(c_n) ≤ liminf C(c_n) = C(Γ).

For the class statement, let F_w be weakly continuous on FR. Then sup_w F_w is lower
semicontinuous, since a supremum of continuous functions is. If it is ≤ C everywhere, item 4
applies at every b.

**Item 5.** By import item 4, O_n = {a ∈ FR : C(a) < C(Γ) + 1/n} is open in FR. It contains K,
so it is dense. Then ∩_n O_n = {C = C(Γ)} is a dense G_δ in FR.

The Bernoulli shift enters only through the imported display. That display rests on the
Abért–Weiss weak containment s ≼ a, also recorded in `abert-weiss-free-actions-weakly-contain-bernoulli`,
together with the monotonicity in `cost-is-constant-on-weak-equivalence-classes`.
