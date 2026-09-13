---
rg: 2
id: every-finitely-presented-torsion-group-is-finite
kind: claim
title: Every finitely presented group in which every element has finite order is finite
distinct_from:
  there-is-a-finitely-presented-infinite-torsion-group: that is the negation of this claim; exactly one of the two holds, and the Problem 1.11 root is established by whichever does.
---

**OPEN.** If a group `Q` has a finite presentation and every element of `Q`
has finite order, then `Q` is finite.

This is the nonexistence answer to Zaremsky Problem 1.11
(`zaremsky-1-11-fp-infinite-torsion-group`). It would also rule out infinite
torsion groups of type F∞, since those are finitely presented.

## Attempts

- Known special classes, where the conclusion holds for class-specific reasons:
  linear groups (Burnside–Schur), hyperbolic groups (infinite ones contain
  elements of infinite order), and residually finite groups of bounded exponent
  (restricted Burnside problem). None of these arguments uses finite
  presentability, so none extends. The obstruction lane z1-11-torsion-block
  owns this side.
- Quotients of finitely presented torsion-by-cyclic groups: finite whenever the
  torsion base is just-infinite, by the construction lane's coinvariant
  analysis. This is a statement about one family of candidates, not a proof of
  this claim.
