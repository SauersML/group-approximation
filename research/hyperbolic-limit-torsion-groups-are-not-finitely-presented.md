---
rg: 2
id: hyperbolic-limit-torsion-groups-are-not-finitely-presented
kind: claim
title: A torsion group obtained as a direct limit of infinite hyperbolic quotients is not finitely presented
distinct_from:
  fp-direct-limit-of-quotients-equals-a-finite-stage: that is the general stabilization lemma for finitely presented limits; this applies it to limits of infinite hyperbolic groups, the method behind every finitely generated torsion monster of Ol'shanskii type.
---

**ESTABLISHED** (proof in `hyperbolic-limit-torsion-groups-are-not-finitely-presented-proof`).

Let `F` be a free group of finite rank and `K_1 <= K_2 <= ...` normal subgroups
such that each `F / K_i` contains an element of infinite order. This holds, for
instance, when each `F / K_i` is an infinite word hyperbolic group. If
`G = F / U_i K_i` is a torsion group, then `G` is not finitely presented.

**Scope.** Ol'shanskii–Sapir (arXiv:math/0208237, p. 3) record that Ol'shanskii's
torsion Tarski monsters and Adian's free Burnside groups "are inductive limits
of word hyperbolic groups". Those constructions, and any construction that
presents a torsion group as such a limit, cannot give Zaremsky Problem 1.11 its
answer. A finitely presented example must be torsion at a finite stage of its
defining sequence.
