---
rg: 2
id: f-dyadic-action-is-not-recurrent
kind: claim
title: The action of Thompson's F on the dyadic rationals is not recurrent, so its inverted orbit has linear mean growth and the recurrence criterion for extensive amenability fails
distinct_from:
  thompson-f-dyadic-action-is-extensively-amenable: that is the open extensive amenability; this proves only that the standard recurrence route to it is unavailable, since the mean inverted orbit is ballistic.
  f-dyadic-ea-iff-inverted-orbit-confinement: that reduces extensive amenability to confinement of the inverted orbit on rare events; this shows the unconditional mean of the inverted orbit is linear, which is compatible with either answer.
artifacts:
  - research/artifacts/hl-f-extensive-amenability-dyadic-2026-09-14.md
---

**ESTABLISHED.** For every non-degenerate symmetric finitely supported probability measure `μ` on `F` with
generating support and every base point `x_0 ∈ D`, the inverted orbit `O_n = {x_0, g_1⁻¹x_0, …, g_n⁻¹x_0}`
of the left random walk satisfies

`(1/n) E|O_n| → P(T = ∞) > 0`, where `T = min{ n ≥ 1 : g_n x_0 = x_0 }`.

Equivalently, `F ↷ D` is **not recurrent**: the induced simple random walk on the dyadic Schreier graph is
transient.

**Consequence.** The recurrence criterion for extensive amenability (recurrent actions are extensively
amenable; Juschenko–Nekrashevych–de la Salle) does not apply to `F ↷ D`. More sharply, the sufficient
condition `(1/n) E|O_n| → 0` fails, so the only surviving route to extensive amenability of `F ↷ D` through
the inverted orbit is the rare-event confinement `f-dyadic-inverted-orbit-is-subballistic-on-rare-events`
(condition (ii) of `f-dyadic-ea-iff-inverted-orbit-confinement`), which is strictly weaker than mean
confinement.

**Input.** Transience of the dyadic Schreier graph is Mishchenko (arXiv:1512.03083): the simple random walk
on it has nontrivial Poisson boundary, hence the graph is non-Liouville, hence transient. This is recorded
as a known obstacle in `thompson-f-dyadic-action-is-extensively-amenable`; this claim upgrades it to the
quantitative statement that the mean inverted orbit is ballistic.

Proof route: `f-dyadic-action-not-recurrent-proof`.
