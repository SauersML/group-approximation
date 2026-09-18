---
rg: 2
id: fpbs-wq-normal-class-critical-spectral-dt-certificate
kind: claim
title: Cayley graphs of nonamenable groups with an infinite amenable wq-normal subgroup admit a critical spectral DT certificate
distinct_from:
  fpbs-nonamenability-bounds-critical-connectivity-operator: that asks for ||T_(p_c)|| < infinity on all nonamenable graphs; this asks for one finite set S whose boundary measure at p_c has spectral radius below one, which implies that bound on the graphs of this class (the converse is open).
  fpbs-critical-sphere-fibre-operator-below-one: that is a norm condition on the full critical two-point function over a hyperbolic quotient; this is a spectral-radius condition on finite-volume connection probabilities with no hyperbolicity.
  fpbs-amenable-wq-normal-relative-subcriticality: that is the relative susceptibility statement; this finite-volume certificate implies it, is blind to H, and also implies the critical l2 bound.
artifacts:
  - research/artifacts/fpbs-spectral-dt-certificate-2026-09-17.md
---

**OPEN.** Let `Gamma` be a nonamenable finitely generated group with an
infinite amenable wq-normal subgroup, and `D` a finite symmetric generating set.
Then there is a finite `S` containing `o` with

```text
sp( rho_Gamma(nu_{S,p_c}) ) < 1,
nu_{S,p}(g) = p * sum_{ {u,v} in Delta S, v = g } P_p(o <->_S u).
```

Equivalently, `p_c < p_sDT` in the notation of
`fpbs-spectral-dt-certificate-bounds-connectivity-operator`.

* **Consequences.** It implies `||T_(p_c)||_{2->2} < infinity` and
  `p_c < p_{2->2}` on these graphs. Through
  `fpbs-quotient-spectral-dt-certificates-are-subgroup-blind` it also implies
  `fpbs-amenable-wq-normal-relative-subcriticality`.
* **Not relative.** By the blindness proposition, the statement does not change
  if `Gamma` is replaced by the Schreier space `H\Gamma`. The subgroup only
  selects the class.
* **Evidence.** On the 3-regular tree `B_3` is a certificate (artifact
  Section 6.3). On amenable groups no certificate exists at `p_c` (Section 6.2).
  No example in the class (for instance `F_2 x Z`) has been checked.
* **How it can fail.** It can fail on a graph with `p_c < p_{2->2}` if
  `p_sDT < p_{2->2}` there, which is the open converse in artifact Section 7.
  It can also fail if some graph of the class has `p_c = p_{2->2}`.
