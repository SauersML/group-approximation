---
rg: 2
id: there-is-a-finitely-presented-infinite-torsion-group
kind: claim
title: There is a finitely presented infinite group in which every element has finite order
distinct_from:
  every-finitely-presented-torsion-group-is-finite: that is the negation of this claim; exactly one of the two holds, and the Problem 1.11 root is established by whichever does.
---

**OPEN.** There is a group `Q` with a finite presentation such that `Q` is
infinite and every element of `Q` has finite order.

This is the construction answer to Zaremsky Problem 1.11
(`zaremsky-1-11-fp-infinite-torsion-group`).

**What an example cannot be.** Nothing here is established yet; the root lists
the standard constraints. The construction side adds two firewalls:

- *direct limits*: a finitely presented direct limit of a sequence of quotients
  equals a finite stage, so an example must be torsion at a finite stage of its
  presentation;
- *torsion-by-cyclic*: killing the stable letter of a finitely presented
  ascending HNN extension of a torsion group produces an infinite torsion group
  only when the endomorphism has an infinite coinvariant quotient.

## Attempts

- Torsion quotients of the finitely presented torsion-by-cyclic groups.
  Grigorchuk's finitely presented ascending HNN extension of the first
  Grigorchuk group, and the finitely presented extensions of groups of
  exponent `n` by a cyclic group of Ol'shanskii–Sapir (arXiv:math/0208237).
  A torsion quotient `Q` of `B*_phi` has `t` of finite order `m`. That makes
  the image of `B` a normal subgroup of index at most `m`, and forces
  `b = phi^m(b)` there. So `Q` is infinite only if the coinvariant group
  `B / <<b^-1 phi^m(b)>>` is infinite. For a just-infinite base this never
  happens, so the Grigorchuk extension is dead. The Ol'shanskii–Sapir base is
  not just-infinite, and its coinvariants are the live test.
- Limits of hyperbolic groups (Ol'shanskii, Ivanov–Ol'shanskii, Coulon, Osin):
  dead. Every stage is an infinite hyperbolic group and so has an element of
  infinite order, while a finitely presented limit equals a stage.
- Golod–Shafarevich presentations: finitely many relators give an infinite
  pro-`p` completion. Making the discrete group torsion needs infinitely many
  relators in every known construction. By the direct-limit firewall, a
  finitely presented torsion example would have to be torsion already at a
  finite stage.
