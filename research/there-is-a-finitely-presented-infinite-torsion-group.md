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
  the image of `B` a normal subgroup of index dividing `m`, and forces
  `b = phi^m(b)` there. So `Q` is infinite only if the coinvariant group
  `B / <<b^-1 phi^m(b)>>` is infinite
  (`ascending-hnn-torsion-quotients-see-only-coinvariants`, established).
  - For a just-infinite base this never happens unless the base is already
    finitely presented (`just-infinite-base-hnn-has-only-finite-torsion-quotients`,
    established).
  - So the Grigorchuk extension is dead
    (`grigorchuk-hnn-extension-has-only-finite-torsion-quotients`, established).
  - The Ol'shanskii–Sapir base is not just-infinite, and its coinvariants are the
    live test: `olshanskii-sapir-hnn-has-infinite-coinvariants` (open), wired
    here by `fp-torsion-via-olshanskii-sapir-coinvariants`. For `m = 1` it is
    Rips' construction as reported by Ol'shanskii–Sapir.
- Limits of hyperbolic groups (Ol'shanskii, Ivanov–Ol'shanskii): dead. Every
  stage is an infinite hyperbolic group and so has an element of infinite
  order, while a finitely presented limit equals a stage
  (`fp-torsion-group-is-no-limit-of-non-torsion-groups`, established).
- Self-similar torsion groups themselves: finitely generated contracting regular
  branch groups are not finitely presented (Bartholdi–Grigorchuk–Šunić,
  arXiv:math/0510294, Theorem 4.7), and neither are torsion spinal groups
  (Corollary 4.5). The remaining self-similar candidates are torsion groups
  outside those classes, and none is recorded.
- No dead `requires: []` route is written into this claim on purpose. The dead
  approaches are recorded as established obstruction claims and cited here, so
  an unestablished invalidator can never make this famous open claim read as
  proved.
- Golod–Shafarevich presentations: finitely many relators give an infinite
  pro-`p` completion. Making the discrete group torsion needs infinitely many
  relators in every known construction. By the direct-limit firewall, a
  finitely presented torsion example would have to be torsion already at a
  finite stage.
