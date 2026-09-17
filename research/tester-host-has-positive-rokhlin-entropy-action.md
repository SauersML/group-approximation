---
rg: 2
id: tester-host-has-positive-rokhlin-entropy-action
kind: claim
title: The Gottschalk tester host admits a free ergodic action of positive Rokhlin entropy
distinct_from:
  leavitt-unit-group-has-positive-rokhlin-entropy-action: that asks the entropy question for the binary Leavitt unit group, which would settle Gottschalk's conjecture only for that group; this asks it for the tester host, whose positive answer settles the conjecture for all groups.
  every-group-has-positive-rokhlin-entropy-action: that quantifies over all countably infinite groups; this is the single host, equivalent to it through tester-host-pos-iff-maximal-bernoulli-rokhlin-entropy and the maximality closure on the tester.
artifacts:
  - research/artifacts/rokhlin-entropy-self-copy-dichotomy-2026-09-12.md
  - research/artifacts/bernoulli-bundle-orbit-relation-entropy-2026-09-17.md
---

**OPEN.** The fixed two-generator finitely presented host `U_*` of `gottschalk-surjunctivity-fixed-two-generator-tester` admits a free ergodic p.m.p. action with positive Rokhlin entropy.

By `tester-host-pos-iff-maximal-bernoulli-rokhlin-entropy`, this is equivalent to `bernoulli-rokhlin-entropy-maximal-on-fixed-tester`. It passes down to every infinite countably generated recursively presented group, including the binary Leavitt unit group.

## Attempts

* **Sofic entropy.** `U_*` contains nonsofic groups, and every known lower bound for Rokhlin entropy runs through sofic entropy.
* **Subgroups.** Positive entropy passes down from `U_*` to its infinite subgroups, not up. Restriction bounds the host's Rokhlin entropy only from above.
* **Scope.** The claim is equivalent to Seward's hypothesis that every countably infinite group has a positive-entropy free ergodic action, given the maximality closure recorded on `bernoulli-rokhlin-entropy-maximal-for-every-group`. It is not known to follow from Gottschalk's conjecture.
* **Orbit-relation reframing (a-gs-tester-host, 2026-09-17).** By `bernoulli-rokhlin-entropy-is-an-orbit-relation-invariant`, `h^Rok_{U_*}(L^{U_*})` equals `E_λ(R_Y) = h(L^{U_*} × Y | B(Y))` for any weakly minimal free Y. This value depends only on the measured relation R_Y. So the hole is equivalent to asking for a relation isomorphic to R_Y with `E_λ > 0`, and by `weakly-minimal-oe-transfers-rokhlin-supremum` INF would transfer from any group Γ whose weakly minimal action has the same relation. Where it dies: every free action orbit equivalent to Y is a nonsofic action. The restriction of Y to the nonsofic subgroup from `finitely-presented-nonsofic-group-exists` gives this by `free-action-containing-nonsofic-group-relation-is-nonsofic`, and it passes to every regenerator by `paunescu-orbit-equivalent-free-actions-share-soficity`. The lower bound on the regenerator W has only two certified sources.
  * Relative sofic entropy: models of `L^Γ × W` restrict to models of W.
  * Seward's equality on a Γ with `h_sup(Γ) = ∞`: every such Γ in the graph is sofic.

  Both die at the step that certifies `E_λ(R_W) > 0`, provided two facts hold. Neither is imported: "sofic models of a free action make it Păunescu-sofic" and "a weakly minimal free action of a sofic group is sofic". Soficity is itself an orbit-relation invariant, so the reframing does not escape the sofic barrier. It moves the barrier from groups to relations. Artifact, Section 3.
