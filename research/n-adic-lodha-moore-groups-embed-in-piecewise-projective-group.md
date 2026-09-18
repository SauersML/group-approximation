---
rg: 2
id: n-adic-lodha-moore-groups-embed-in-piecewise-projective-group
kind: claim
title: Kodama's n-adic Lodha–Moore groups G_0(n) embed in the group of piecewise projective homeomorphisms of the line
distinct_from:
  higman-group-embeds-in-no-lodha-moore-or-monod-group: that excludes Higman's group from the Lodha–Moore groups and from Monod's H(R), via piecewise real-analytic circle groups; this asks whether the n-adic generalizations G_0(n) are themselves piecewise projective, which that obstruction would then cover.
artifacts:
  - research/artifacts/gq-bh-openq-lists.md
---

**OPEN.** Y. Kodama, *Distorted and undistorted subgroups of the Lodha–Moore group*,
arXiv:2602.04839v1 (4 Feb 2026), the Remark closing the proof of Theorem `theorem_BS_distorted`, TeX
l.866–870:

> In [Kodama 2023], the author defined a generalization of the group $G_0$, called
> $G_0(n)$. Since $G_0$ is a subgroup of $G_0(n)$, the group $BS(1,2)$ is also a
> subgroup of $G_0(n)$. However, to the best of our knowledge, it is not known whether
> $G_0(n)$ is a subgroup of $\PPSL$ or not.

Here `PPSL` is the group of piecewise `PSL_2(R)` homeomorphisms of `R`.

**Why it is recorded here.**
- A positive answer would put every `G_0(n)` inside Monod's `H(R) ≤ PA_+(S^1)`. Then
  `higman-group-embeds-in-no-lodha-moore-or-monod-group`, via
  `higman-group-embeds-in-no-piecewise-analytic-circle-group`, would extend to show
  Higman's group has no nontrivial homomorphism to any `G_0(n)`.
- A negative answer would give Lodha–Moore-type groups outside the piecewise projective
  world. For those, the Oberwolfach question 110 (Higman's group into Lodha–Moore groups)
  would reopen.
- A weaker target suffices for the Higman-group application: an embedding into some
  group of piecewise real-analytic homeomorphisms of the circle.

## Attempts

**Attempt 1 (bh-garrido-kodama, 2026-09-18): the natural codings are excluded; the abstract question stays OPEN.**
- **Source.** Kodama asked this question earlier too: arXiv:2204.08230v2, l.167, where it is
  phrased as whether `G_0(n)` is a subgroup of Monod's `H`. Definitions are at l.818–880.
- **Result.** `n-adic-lodha-moore-groups-have-no-analytic-tree-coding` (lane proof). For `n ≥ 3`,
  no analytic tree coding of `C_n` makes `y_((n−1)0)` piecewise analytic. That rules out every
  digit recoding into Lodha–Moore's coding, every n-ary Farey or Stern–Brocot coding, and every PL
  coding.
- **Mechanism.** `analytic-codings-make-contracting-recursions-analytic`. The contracting rule
  `y(00ζ) = 0y(ζ)` moves every breakpoint of `y` to `ψ(0^∞)`. The finitary rule `y(0kζ) = kζ`
  then forces `y = g_0^(−1)` on one side of that point, and the contracting rule forces `g_0 = id`
  there.
- **What a positive answer needs.** A piecewise-projective action of `G_0(n)` in which the cone
  structure of `F(n)` is not coded analytically. For example, the prefix maps of `F(n)` would have to
  act by non-analytic cone maps, or the action would not factor through `C_n` at all. I found no
  candidate.
- **The Higman application.** Extending `higman-group-embeds-in-no-lodha-moore-or-monod-group` to
  `G_0(n)` therefore needs a direct argument, not a transfer through `H`. The weaker target of a
  piecewise-analytic circle action is excluded along the same natural route.
