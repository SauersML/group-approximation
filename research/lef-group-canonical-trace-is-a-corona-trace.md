---
rg: 2
id: lef-group-canonical-trace-is-a-corona-trace
kind: claim
title: "A canonical corona trace forces operator MF, and every LEF group's canonical trace is a corona trace"
distinct_from:
  lef-implies-operator-mf: that proves LEF gives a faithful corona homomorphism; this records that the same models realize the canonical trace, and that trace control in turn forces MF.
  gkmp-mf-is-trace-regular-not-bare-operator-mf: that separates bare operator MF from the three-clause GKMP notion; a canonical corona trace is exactly clauses (1) and (2), without the reduced-norm clause (3).
artifacts:
  - research/artifacts/un-traces-2026-09-13-part1.md
---

**ESTABLISHED (unreviewed).**

**Definition.** Let Q_d = ∏_k M_{d_k}/⊕_k M_{d_k} and ω a free ultrafilter, and put
tr_ω([x_k]) = lim_ω tr_{d_k}(x_k) (well defined since norm-null sequences have trace → 0). A trace τ on
C*_max(G) is a **corona trace** if τ = tr_ω∘Φ for some d, ω and unital *-homomorphism Φ: C*_max(G) → Q_d.

**Theorem.** Let G be countable.
- (a) If the canonical trace τ_G is a corona trace, G is operator MF.
- (b) If G is LEF, τ_G is a corona trace.

So LEF ⟹ (τ_G a corona trace) ⟹ operator MF. The middle notion is the trace-level shadow of an MF
approximation that also sees the regular character.

Proof route: `lef-group-canonical-trace-is-a-corona-trace-proof`. Credit: (a) is the argument in the proof
of `non_mf_groups_exist.tex` Thm l.1349, and (b) is the construction of `lef-implies-operator-mf` with the
trace recorded.
