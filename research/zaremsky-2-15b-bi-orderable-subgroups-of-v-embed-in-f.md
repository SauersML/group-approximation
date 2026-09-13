---
rg: 2
id: zaremsky-2-15b-bi-orderable-subgroups-of-v-embed-in-f
kind: claim
title: "Zaremsky Problem 2.15, reposed: does every bi-orderable subgroup of V with no non-abelian free subgroups embed into F?"
root: true
distinct_from:
  zaremsky-2-15-torsion-free-subgroups-of-v-embed-in-f: that is the numbered problem with torsion-free hypothesis, answered no by the Klein bottle group; this is Zaremsky's suggested repost with the stronger hypothesis bi-orderable, which the Klein bottle group does not satisfy
---

M. C. B. Zaremsky, *Some open problems* (version of July 12, 2026,
https://zaremsky.github.io/open_problems.pdf), Section 2, Problem 15, update of
April 3, 2026, verbatim: "No, Corentin Bodart points out the (torsion-free)
Klein bottle group embeds in `V`, but cannot embed in `F` since it is not
bi-orderable. So perhaps the question should be re-posed with “torsion-free”
replaced by “bi-orderable”."

The reposed question: does every bi-orderable subgroup of Thompson's group `V`
with no non-abelian free subgroups embed into Thompson's group `F`?

This claim is the question. It is established only through an answer route:

- **Yes**: `zaremsky-2-15b-by-yes` requires
  `biorderable-subgroups-of-v-without-free-subgroups-embed-in-f`.
- **No**: `zaremsky-2-15b-by-no` requires
  `biorderable-subgroup-of-v-without-free-subgroups-not-in-f`.

Never write a `requires: []` route into this claim.

**Reading.** "Bi-orderable" means the abstract group admits a total order
invariant under left and right multiplication; the order need not be related to
the action of `V` on the Cantor set. "Embed into `F`" means an injective
homomorphism into `F`. A counterexample is a group `G` isomorphic to a subgroup
of `V`, bi-orderable, with no non-abelian free subgroup, and isomorphic to no
subgroup of `F`. The question is not local: `G` may be infinitely generated, and
a "no" answer given by a finitely generated `G` is the natural target.

**Why bi-orderability binds.** `F` is bi-orderable, so bi-orderability is
necessary. It also rules out the finite-extension twists behind the Klein bottle
example: in a bi-orderable group `[g^k, h] = 1` forces `[g, h] = 1`, so a
bi-orderable virtually abelian group is abelian.

**Status (2026-09-13).** Open. z-status-b found nothing on this repost
(`research/artifacts/zp-open-status-sections-2-4-2026-09-13-part1.md`). A
relevant recent tool is Bodart–D'Angeli–Perego–Rodaro, arXiv:2608.02111: a
finitely generated group embeds in `V` iff it has a faithful context-free
action, and every finitely generated subgroup of `V` is virtually abelian or
contains a free non-abelian semigroup.

## Attempts

- 2026-09-13 (z2-15b-biorderable), plan. Two sides:
  1. **No.** Find a bi-orderable solvable group in `V` violating a necessary
     condition for subgroups of `F`. Conditions this lane proves or collects:
     non-abelian nilpotent groups do not embed in `PL_+(I)`; `BS(1,n)` (n ≥ 2)
     and hyperbolic `Z^2 ⋊_A Z` do not embed in `PL_+(I)`; `Z ≀ Z^2` does not
     embed in `F`. Each candidate must then be tested inside `V`, where the
     analogous germ arguments at attracting periodic points apply to some but
     maybe not all of them.
  2. **Yes.** Prove embedding theorems for classes: subgroups of `T` via
     Margulis' invariant measure for circle actions without free subgroups, and
     solvable subgroups of `V` via revealing-pair dynamics.
