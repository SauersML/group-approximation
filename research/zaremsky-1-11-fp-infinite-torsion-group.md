---
rg: 2
id: zaremsky-1-11-fp-infinite-torsion-group
kind: claim
title: "Zaremsky Problem 1.11 resolved: is there a finitely presented (or F_infinity), infinite, torsion group?"
root: true
distinct_from:
  fp-infinite-simple-amenable-group: that is Problem 1.10, which asks for a finitely presented infinite simple amenable group; this asks for a finitely presented infinite group all of whose elements have finite order, with no simplicity or amenability condition.
---

M. C. B. Zaremsky, *Some open problems* (version of July 12, 2026,
https://zaremsky.github.io/open_problems.pdf), Section 1, Problem 11, verbatim:
"Find a finitely presented (or F∞), infinite, torsion group."

This claim is the question. It is established only through an answer route:

- **Yes**: `zaremsky-1-11-by-construction` requires
  `there-is-a-finitely-presented-infinite-torsion-group`.
- **No**: `zaremsky-1-11-by-nonexistence` requires
  `every-finitely-presented-torsion-group-is-finite`.

Never write a `requires: []` route into this claim.

**Reading.** A torsion (periodic) group is one in which every element has
finite order. "Find" asks for an example, so the construction answer is an
explicit finitely presented infinite torsion group. The parenthetical "(or F∞)"
names the stronger form `there-is-an-infinite-torsion-group-of-type-f-infinity`.
Type F∞ implies type F_2, which is finite presentability, so that form feeds
the finitely presented one through
`fp-infinite-torsion-group-from-f-infinity-example`. The answer "no such group
exists" is `every-finitely-presented-torsion-group-is-finite`, which settles
both forms.

**Status.** A classical open problem. Ol'shanskii and Sapir
(arXiv:math/0208237, §1.1, p. 3) call "finding a finitely presented infinite
torsion group" "probably the most famous problem" among the finitely presented
"monsters", and remark that the finitely generated examples are limits of
hyperbolic groups, "and there is no hope to construct finitely presented
examples as such limits". Finitely generated infinite torsion groups exist
(Golod–Shafarevich, Grigorchuk, Ol'shanskii, Osin arXiv:2211.09989); none of the
known ones is finitely presented. The nearest finitely presented objects are
torsion-by-cyclic: Ol'shanskii–Sapir build a finitely presented extension of a
group of exponent `n >> 1` by a cyclic group (arXiv:math/0208237, abstract).
A bounded check on 2026-09-13 (one web search, arXiv abstracts only) found no
answer; the list's own date is July 12, 2026. `z-status-a` runs the fuller
literature sweep.

**Standard constraints on a construction answer** (each still to be recorded as
its own node):

- finitely generated linear torsion groups are finite (Burnside–Schur), so an
  answer is not linear;
- infinite hyperbolic groups contain elements of infinite order, so an answer
  is not hyperbolic;
- finitely generated residually finite groups of bounded exponent are finite,
  by the positive solution of the restricted Burnside problem
  (`restricted-burnside-finiteness`), so an answer of bounded exponent is not
  residually finite.

## Attempts

- 2026-09-13, construction side (lane z1-11-torsion-build): the torsion-by-cyclic
  route. A torsion quotient of an ascending HNN extension `B*_phi` sees only
  the coinvariant groups `B / <<b^-1 phi^m(b)>>`. When `B` is just-infinite they
  are finite, and this covers every finitely generated torsion branch group,
  the first Grigorchuk group among them. Nodes land in the next landing.
- 2026-09-13, limits of hyperbolic groups: a finitely presented direct limit of
  a sequence of quotients equals one of its finite stages. So a torsion limit
  of infinite hyperbolic groups is never finitely presented. Node lands in the
  next landing.
- Obstruction side: lane z1-11-torsion-block.
