---
rg: 2
id: infinite-kazhdan-group-with-mf-reduced-cstar
kind: claim
title: Some infinite Kazhdan group has MF reduced C-star algebra
root: true
distinct_from:
  kt-double-reduced-cstar-is-mf: that is reduced MF of one nonsofic double; this asks it only for an infinite Kazhdan group, which the double would supply but which is necessary and possibly easier.
  reduced-mf-kazhdan-subgroup-gate: that proves this claim is necessary for the reduced-MF route to the known nonsofic groups; this is the open existence question itself.
---

**OPEN.**  Exhibit an infinite group `Gamma` with property (T) such that
`C*_r(Gamma)` admits an injective *-homomorphism into
`prod_n M_(d_n) / sum_n M_(d_n)`.

By `reduced-mf-kazhdan-subgroup-gate` this is necessary before any nonsofic
group produced by the known criteria can have MF reduced C-star algebra, so it
gates `nonsofic-reduced-mf-group-finite-amenable-radical` along those
mechanisms.

**Contrast with MF traces.**  The weaker operator-norm target
`reduced-amalgam-canonical-trace-is-mf` has no such vertex gate.  For a
residually finite `Gamma`, take finite-index normal subgroups `N_n` decreasing
with trivial intersection.  The regular representations of `Gamma/N_n` are
genuine finite-dimensional representations with normalized trace
`1_(g in N_n) -> delta_e(g)`, so the regular trace is already an MF trace.
Reduced MF additionally demands the reduced norms, which finite quotients do
not supply: the constants carry the norm-one eigenvalue of every averaging
operator.

## Attempts

* **Genuine representations of `SL_d(Z)`, `d >= 4`.**  Dead.  Magee--de la
  Salle (arXiv:2312.03220, C. R. Math. 362 (2024) 903--910): every
  finite-dimensional unitary representation of `SL_4(Z)` has a nonzero
  `SL_2(Z)`-invariant vector, so no sequence of representations embeds the
  reduced algebra.  `SL_3(Z)` is open.  Approximate models are not excluded.
* **Known strongly convergent classes.**  Dead as sources.  Van Handel's survey
  (arXiv:2510.12520, Section 2.3) lists free groups, surface groups,
  right-angled Artin groups and groups virtually embedding in them, records the
  `SL_4(Z)` obstruction, and states that which groups admit strongly convergent
  representations remains largely open.  The listed groups are a-T-menable, and
  amenable groups are too, so none contains an infinite Kazhdan subgroup.
  Amalgam closure theorems cannot create one: a Kazhdan group acting on a tree
  fixes a vertex.
* **Nontrivial parts of finite-quotient regular representations.**  Open.
  (T) supplies a uniform spectral gap, but strong convergence asks for the
  regular-representation norm of every group-ring element, which (T) does not
  give.
* **Approximate operator-norm models.**  No construction and no obstruction
  recorded.
