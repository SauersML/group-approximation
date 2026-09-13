---
rg: 2
id: equicontinuous-action-full-group-fg-subgroups-are-rf
kind: claim
title: Finitely generated subgroups of the topological full group of an equicontinuous Cantor action are residually finite, so no infinite simple group lives there
distinct_from:
  residually-finite-minimal-actions-have-lef-full-groups: That imports Xin Ma's theorem that full groups of minimal topologically free residually finite actions are LEF; this assumes neither minimality nor topological freeness, only equicontinuity, and concludes residual finiteness of every finitely generated subgroup.
  periodic-approximable-subshifts-host-no-fp-simple-group: That removes full groups of free subshifts with periodic approximations; this removes full groups of equicontinuous actions, which are expansive only when finite, and allows arbitrary isotropy.
artifacts:
  - research/artifacts/solve-fp-amenable-nonfree-hosts-2026-09-13.md
---

**ESTABLISHED** (direct proof: `equicontinuous-full-group-rf-via-invariant-ultrametric-proof`).
It has not been independently reviewed, and no novelty is claimed.

**Setting.**
- A group `Λ` acts by homeomorphisms on a Cantor space `X`, equicontinuously: for a
  compatible metric `d` and every `ε > 0` there is `δ > 0` such that `d(x, y) < δ` implies
  `d(λx, λy) < ε` for every `λ ∈ Λ`.
- `[[Λ ~ X]]` is the group of homeomorphisms `g` of `X` having a continuous cocycle
  `c_g : X -> Λ` with `g(x) = c_g(x)·x`.
- No freeness, topological freeness or minimality is assumed.

**Theorem.** Every finitely generated subgroup `Γ ≤ [[Λ ~ X]]` is residually finite.
So `[[Λ ~ X]]` contains no finitely generated infinite simple group. In particular it
contains no finitely presented infinite simple group.

**Groupoid form.** An element of the topological full group of the groupoid of germs of
`Λ ~ X` agrees near each point with some element of `Λ`. By compactness it has a locally
constant cocycle, so that full group is `[[Λ ~ X]]`. The theorem therefore covers groupoids
of germs with isotropy, not only transformation groupoids.

**What it removes from case (S2)** of `fp-infinite-simple-amenable-group`.
- **Rooted trees.** Any group of automorphisms of a locally finite rooted tree acts on the
  boundary by isometries of the standard ultrametric. So the full group of its germ groupoid
  hosts no finitely generated infinite simple group, with or without isotropy. This includes
  the germ groupoids of bounded automaton groups, such as the Grigorchuk and Basilica groups.
- **Odometers and profinite actions.**
- **Isometries.** Every action by isometries of a compatible metric.

It kills the candidate suggested for step 2 of lane solve-fp-amenable-nonfree-hosts: the
alternating full group of the germ groupoid of a bounded automaton group.
