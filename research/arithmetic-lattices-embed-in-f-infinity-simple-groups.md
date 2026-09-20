---
rg: 2
id: arithmetic-lattices-embed-in-f-infinity-simple-groups
kind: claim
title: Every group commensurable with an irreducible arithmetic lattice in a semisimple Lie group, in particular every lattice in Sp(n,1) or F_4^(-20) and so every such cocompact hyperbolic Kazhdan group, embeds in a simple group of type F_∞
distinct_from:
  arithmetic-lie-lattices-have-faithful-bs-members: that supplies the faithful Hecke member and concludes only membership in the permutational class B_A (finitely presented simple envelopes), for lattices in groups with trivial center; this feeds that member into the F_n form of Bux–Llosa Isenrich–Wu Theorem 11.1 for every n, gets one envelope of type F_∞, and passes to finite center through commensurability.
  surface-generalized-bs-groups-satisfy-boone-higman: that is the same F_∞ upgrade for closed surface groups only; this runs it for every arithmetic lattice and names the Kazhdan hyperbolic consequence.
  a2-lattices-embed-in-fp-simple-groups: that covers cocompact groups on Ã₂ buildings (Kazhdan, not hyperbolic, possibly non-linear) through Li's theorem; this covers lattices in real Lie groups, whose cocompact rank-one members are hyperbolic.
  bounded-defect-free-full-contracting-rsgs-are-f-infinity: that is the rational-similarity route toward BBMZ Question 1.2, which likely cannot reach Kazhdan inputs (bbmz-hosts-with-higher-dimensional-boundary-are-unbounded); this reaches the Kazhdan hyperbolic lattices without any rational similarity group.
artifacts:
  - research/artifacts/gq-bh-bh-free-extensions-bliw-section-11-12.md
  - research/artifacts/gq-bh-q12-alt-host-routes.md
---

**OPEN (proof claimed, under review).** The claimed proof is
`arithmetic-lattices-embed-in-f-infinity-simple-groups-proof`, a lane proof assembling landed nodes.
A referee (bh-ref-t0) is checking it.

**Priority: attribution to Llosa Isenrich–Schesler–Wu.** Their arXiv:2510.01952, Theorem 1.4 with
Remark 1.5, as quoted by a summarizing fetch of the arXiv HTML and not read at source, says:

> "Let H be a finitely generated subgroup of GL_n(ℚ). There exists a simple group G that has the
> same finiteness properties as H, H is a subgroup of G, and G admits a quasi-retract onto H."

Remark 1.5 extends it to finitely generated subgroups of `GL_n(ℚ̄)`. Every lattice in `Sp(n,1)` or
`F_4^{(-20)}` is arithmetic, so it is linear over a number field: a finite-index subgroup is, and a
faithful induced representation passes this to the lattice. Each is also of type `F_∞`. So the
Kazhdan hyperbolic consequence below already follows from their theorem, although they do not state
it for lattices. This node is an independent second route, through Bux–Llosa Isenrich–Wu trees
rather than Röver–Nekrashevych groups, and claims no priority.

## Statement

Let `L` be a connected semisimple real Lie group with finite center and no compact factors, and let
`Γ ≤ L` be an irreducible arithmetic lattice. Then every group `K ∈ BS_Γ` (Bux–Llosa Isenrich–Wu:
fundamental groups of finite graphs of groups whose vertex and edge groups are abstractly
commensurable with `Γ`, with finite-index edge inclusions) embeds in a simple group of type `F_∞`.
In particular `Γ` itself, and every group abstractly commensurable with `Γ`, does.

## Instances

1. **Kazhdan hyperbolic lattices.** Every lattice in `Sp(n,1)` or `PSp(n,1)`, `n ≥ 2`, and every
   lattice in `F_4^{(-20)}`, embeds in a simple group of type `F_∞`. All these lattices are
   arithmetic (Corlette 1992 for `Sp(n,1)`, Gromov–Schoen 1992 for `F_4^{(-20)}`; cited, not
   re-read). The cocompact ones are hyperbolic groups with property (T): hyperbolic because they act
   geometrically on a negatively curved symmetric space, Kazhdan because `Sp(n,1)`, `n ≥ 2`, and
   `F_4^{(-20)}` have (T) (Kostant; cited). So these Kazhdan hyperbolic groups have `F_∞` simple
   hosts. Such groups are never cubulated (Niblo–Reeves), so the `2V` route through special cube
   complexes does not reach them.
2. **Higher rank.** Every irreducible lattice in real rank `≥ 2` (Margulis arithmeticity, cited),
   for example `SL_n(Z)` and `Sp_{2n}(Z)` for `n ≥ 3` and `n ≥ 2`.
3. **Arithmetic real and complex hyperbolic lattices** in `SO(n,1)` and `SU(n,1)`.

## Scope and limits

- **Residual finiteness is the gate.** The route goes through faithful actions on locally finite
  trees, so every input is residually finite (`finite-index-edge-hnn-embeds-in-fp-simple-group`,
  items L1 and L4). Kazhdan hyperbolic groups not known on main to be residually finite, such as the
  Caprace–Conder–Kaluba–Witzel group `𝓗_31` (arXiv:2011.09276, Theorem 1.2) or random groups at
  density in `(1/3, 1/2)`, stay open.
- **Non-arithmetic lattices** (only in `SO(n,1)` and `SU(n,1)`) have discrete commensurator, and
  `commensurator-rigid-groups-lack-faithful-bs-members` records that this route gives nothing there.
- **BBMZ Question 1.2 itself** asks about full contracting rational similarity groups. That question
  is not settled here; this node gives a different host for the lattice subclass of the
  hyperbolic inputs, which is the part of BBMZ survey Problem 5.3 ("even of type `F_∞`?") it
  touches.
- **Trust surface.** Bux–Llosa Isenrich–Wu Theorems 10.5 and 11.1 and their `n`-independence (proofs
  not re-checked here), and the cited arithmeticity and property (T) theorems.
