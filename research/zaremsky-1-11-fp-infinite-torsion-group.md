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
  route. `ascending-hnn-torsion-quotients-see-only-coinvariants` (established):
  a torsion quotient of an ascending HNN extension `B*_phi` is a finite
  extension of a quotient of a coinvariant group `B / <<b^-1 phi^m(b)>>`.
  - `just-infinite-base-hnn-has-only-finite-torsion-quotients` (established):
    for just-infinite bases, all finite unless the base is already finitely
    presented. This covers finitely generated torsion weakly branch bases.
  - `grigorchuk-hnn-extension-has-only-finite-torsion-quotients` (established):
    Grigorchuk's finitely presented extension is dead.
  - Live test: `olshanskii-sapir-hnn-has-infinite-coinvariants` (open), wired by
    `fp-torsion-via-olshanskii-sapir-coinvariants`.
- 2026-09-13, limits of hyperbolic groups: dead.
  `fp-direct-limit-of-surjections-stabilizes` and
  `fp-torsion-group-is-no-limit-of-non-torsion-groups` (established, lane
  z1-11-torsion-block): a torsion limit through infinitely many stages with
  elements of infinite order, e.g. infinite hyperbolic stages, is never finitely
  presented.
- Obstruction side: lane z1-11-torsion-block.
- 2026-09-17, inverter (lane sw-090): covers of known branch torsion groups.
  A counterexample has a just-infinite torsion quotient; the natural
  certificate is a surjection onto a known torsion branch group.
  - `self-similar-spinal-groups-not-fp-torsion-quotients` (proposed established):
    a section cocycle on the free group climbs from `A * B` to the kernel and
    lifts infinite order. No self-similar spinal group (Grigorchuk, Gupta-Sidki,
    torsion GGS, Fabrykowski-Gupta) is a quotient of a finitely presented
    torsion group. This route is dead for that class. For the first Grigorchuk
    group and `G_omega` this was known in the stronger form
    `fp-covers-of-grigorchuk-groups-are-large`; that import does not cover the Gupta-Sidki and GGS cases.
  - `contracting-torsion-interior-at-finite-radius` (proposed established): for
    any contracting self-replicating finite-state group `J`, the same holds
    unless the single truncated presentation `G_rho0(J)` at an explicit radius is
    torsion. That is the whole remaining question for this class. This is the
    torsion analogue of Benli-Grigorchuk-de la Harpe Theorem 1.9. Check:
    `experiments/spinal-section-cocycle-2026-09-17/`.
