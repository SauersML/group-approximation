---
rg: 2
id: every-hyperbolic-group-is-a-limit-of-isolated-groups
kind: claim
title: Every word hyperbolic group is a limit of isolated groups (Cornulier--Guyot--Pitsch Question 2)
requires:
  - limits-of-isolated-groups-basic-closure
distinct_from:
  every-decidable-group-is-a-limit-of-isolated-groups: that is Question 1 for all groups with solvable word problem; this is its hyperbolic case.
  hyperbolic-groups-satisfy-boone-higman: that embeds a hyperbolic group in a finitely presented simple group (BBMZ); this asks for nearby isolated QUOTIENTS, which that embedding does not provide.
---

**OPEN.**

**The printed question.** Cornulier--Guyot--Pitsch, arXiv:math/0511714v2, p. 11, verbatim:

> "Question 2. Is every word hyperbolic group a limit of isolated groups?"
>
> "Note that a word hyperbolic group has solvable word problem. The following stronger
> question is open: is every word hyperbolic group residually finite?"

**Reduction.** A hyperbolic group is finitely presented, so by
`limits-of-isolated-groups-basic-closure` item 4, `G` is a limit of isolated groups iff for
every finite `F ⊂ G − {1}` it has a finitely presented, finitely discriminable quotient
avoiding `F`.
- Infinite hyperbolic groups are never finitely discriminable (CGP Proposition 8), so the
  quotients must be finite, or infinite and non-hyperbolic.
- Residually finite hyperbolic groups are limits of their finite quotients, so they satisfy the
  question (item 2). This covers every hyperbolic group known to be residually finite, e.g.
  cubulated hyperbolic groups (virtually special by Agol, hence linear); recalled, not re-read
  at source.
- So a negative answer would produce a hyperbolic group that is not residually finite, which is
  itself a famous open problem. A positive answer is implied by residual finiteness of all
  hyperbolic groups and is strictly weaker.

**Open.** A proof that avoids residual finiteness: for every hyperbolic `G` and finite
`F`, an infinite finitely presented finitely discriminable quotient avoiding `F` (for example
an infinite finitely presented simple or monolithic quotient), or a finite one.
