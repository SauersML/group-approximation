---
rg: 2
id: nested-rigid-defects-live-in-nonsofic-kazhdan-groups
kind: claim
title: A nested nontrivial rigid defect lives inside its Kazhdan group, which is then nonsofic with a non-normal centralizer
distinct_from:
  sofic-groups-kill-rigid-compression-defects: that forbids nontrivial rigid defects in sofic ambient groups; this shows the nested ones need no ambient group at all, since the commuting element is forced into the Kazhdan group, so the obstruction is a statement about that one group.
  leavitt-units-carry-nested-rigid-defect: that exhibits one nested defect over the Leavitt algebra; this proves what every nested defect forces on its host.
artifacts:
  - research/artifacts/defect-window-automata-2026-09-12.md
---

**ESTABLISHED** by `nested-defects-in-kazhdan-groups-proof`.

**Setting.** `Gamma <= G <= H` is a rigid pair: `Gamma` and `G` are Kazhdan, and `Gamma`
is infranormal in `G`. Also `t in G`, `z in C_H(Gamma)` and `gamma in Gamma` satisfy

    w = t z t^-1 in Gamma,      [w, gamma] != 1.

**Conclusions.**

1. `z` lies in `G`. So the defect is a rigid defect of the pair `Gamma <= G <= G`.
2. `C_G(Gamma)` is not normal in `G`.
3. `G` is not sofic.
4. Nested nontrivial defects exist exactly when some `t in G` has
   `t (C_G(Gamma) ∩ t^-1 Gamma t) t^-1` not contained in `Z(Gamma)`.
5. `nested-rigid-defects-force-nonsurjunctivity` is equivalent to its case `H = G`: a
   strict pair over the subgroup `G` runs over every group containing it.

**Consequence.** A refutation of the nested-defect criterion needs a surjunctive group
containing a nonsofic Kazhdan group that has a nested defect. The criterion is not about
lamps or ambient extensions. It is about Kazhdan groups where Kun--Thom Theorem B fails
in the nested form.
