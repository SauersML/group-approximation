---
rg: 2
id: linear-groups-over-q-are-quasi-retracts-of-simple-groups
kind: claim
title: Every finitely generated subgroup of GL_n(Q) is a subgroup and a quasi-retract of a simple group with the same finiteness properties
distinct_from:
  fp-self-similar-groups-embed-in-fp-simple-groups: that embeds finitely presented self-similar groups in finitely presented simple groups, with no coarse control; this gives, for linear inputs over Q, a simple Rover--Nekrashevych host that quasi-retracts onto the input, so finiteness properties and Dehn-function lower bounds pass up.
  rover-nekrashevych-simple-groups-are-not-lef-or-torsion-free: that records obstructions inside Rover--Nekrashevych commutator subgroups, citing the same paper for its infinitely presented examples; this imports the paper's main embedding theorem itself.
---

**ESTABLISHED (literature import).**

> **Theorem 1.4 = Theorem 7.1** (C. Llosa Isenrich, E. Schesler, X. Wu,
> *Infinitely presented simple groups separated by homological finiteness
> properties*, arXiv:2510.01952v1, 2 Oct 2025). Let H be a finitely generated
> subgroup of GL_n(Q) for some n ∈ N. There exists a simple group G that has the
> following properties: (1) G has the same finiteness properties as H, (2) H is a
> subgroup of G, (3) G admits a quasi-retract onto H.

**Reading of (1).** The paper uses "finiteness properties" for the types `F_n`,
`FP_n(R)`, `F_∞` and `FP_∞(R)`, as in its Theorem 1.1 (= 7.2). No separate
definition was found in §7. Its Corollary 1.7 = 7.4 says "Every (high-dimensional)
Dehn function of a subgroup of GL_n(Q) arises as a lower bound on the corresponding
Dehn function of a simple group with the same finiteness properties", which
presupposes that `G` is finitely presented whenever `H` is. This node uses (1) only
in that form: `H` of type `F_2` ⇒ `G` of type `F_2`.

**Scope.**
- The simple groups are Rover–Nekrashevych groups of self-similar split extensions
  of `H` (p. 12).
- Remark 1.5 extends it to subgroups of `GL_n(Q̄)`. Question 1.10 asks the same for
  `GL_n(C)` and is open.
- p. 4: "the fastest known Dehn function of a linear group is exponential", and a
  recursive upper bound "conjectured to exist by Gersten and Riley [GR05,
  Conjecture 8.7]". So this theorem gives superexponential Dehn functions for simple
  groups only through `fp-linear-groups-realize-every-recursive-dehn-lower-bound`.

DERIVATION
linear-groups-quasi-retract-of-simple-citation
