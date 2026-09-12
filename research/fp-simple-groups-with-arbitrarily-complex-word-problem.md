---
rg: 2
id: fp-simple-groups-with-arbitrarily-complex-word-problem
kind: claim
root: true
title: For every recursive time bound some finitely presented simple group has a harder word problem
distinct_from:
  simple-envelope-forces-solvable-word-problem: that says every finitely presented simple group has solvable word problem; this asks that those solvable word problems are not uniformly bounded by any recursive time function.
  complexity-bounded-host-classes-are-not-universal: that is the established non-universality theorem for bounded host classes; this is the open existence statement for the specific class of all finitely presented simple groups, which the conjecture would force.
artifacts:
  - research/artifacts/boone-higman-self-similar-and-complexity-2026-09-11.md
---

**OPEN.** For every recursive `T: N -> N` there is a finitely presented simple
group `S` whose word problem has no algorithm running in time
`C*T(C*l) + C*l + C` for any constant `C`.

Every finitely presented simple group has solvable word problem
(`simple-envelope-forces-solvable-word-problem`), so this asks only that the
class have no uniform recursive complexity bound. By
`complex-fp-simple-groups-from-boone-higman` it is a **necessary consequence**
of `boone-higman-conjecture`. A proof of the conjecture must therefore, among
other things, construct finitely presented simple groups beyond every recursive
time bound. That is a concrete test for any proposed universal envelope: its
word problems must be unboundedly complex, i.e. the construction must consume
the input's algorithm, as
`compilers-cannot-drop-the-decidability-hypothesis` already says in a
different form.

It is a root because it is independently well posed, strictly weaker than the
conjecture, and not implied by any established node here.

## Attempts

1. **Twisted Brin--Thompson groups over complex actors.** A finitely
   presented group with a type (A) action whose word problem beats `T` would
   give a simple example through
   `type-a-action-gives-boone-higman-for-subgroups`. The candidate actors in
   this graph are the shift envelope `infinite-shift-higman-compiler`, the
   shell envelopes `perfect-decidable-inputs-have-fp-shell-envelopes`, and the
   fiber-product data `universal-fiber-product-data-for-word-problem-groups`.
   All are open.
2. **Finitely presented self-similar hosts.** Via
   `fp-self-similar-groups-embed-in-fp-simple-groups`, it would suffice to
   embed algorithmically complex finitely presented residually finite groups
   in finitely presented self-similar groups, a special case of
   `every-fp-rf-group-embeds-in-fp-self-similar-group`. By its condition
   (N2) those hosts cannot be automaton groups.
3. **Classical Thompson-like hosts.** *Dies as a method* by
   `complexity-bounded-host-classes-are-not-universal`: any family sharing
   one recursive bound, such as all rational homeomorphism groups, cannot
   supply the needed examples.
