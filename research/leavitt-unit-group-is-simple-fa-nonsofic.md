---
rg: 2
id: leavitt-unit-group-is-simple-fa-nonsofic
kind: claim
title: The binary Leavitt unit group is a finitely presented simple property-FA nonsofic group
distinct_from:
  openai-leavitt-unit-nonsofic: that is the nonsoficity alone; this bundles the four properties finitely presented, simple, property FA and nonsofic, which are exactly the hypotheses of the fixed-host permanence obstruction.
  binary-leavitt-unit-group-is-simple: that is simplicity alone; this adds finite presentation, property FA and nonsoficity.
  sofic-permanence-closure-omits-simple-fa-nonsofic-groups: that is the abstract closure theorem about the class avoiding a fixed such group; this is the concrete witness that the binary Leavitt unit group is one such group.
  leavitt-unit-group-nonsurjunctive: that seeks an injective non-surjective automaton on this group; this records its four structural properties and says nothing about cellular automata.
artifacts:
  - research/artifacts/gottschalk-other-hosts-2026-09-12.md
---

ESTABLISHED. `R^x = L_{F_2}(1,2)^x` is finitely presented, simple, has Serre's
property FA, and is not sofic. So it is one of the groups `Sigma` in the
hypothesis of `sofic-permanence-closure-omits-simple-fa-nonsofic-groups`: a
finitely presented simple nonsofic group with property FA.

- Finitely presented: `leavitt-unit-group-finitely-presented`.
- Simple: `binary-leavitt-unit-group-is-simple`.
- Not sofic: `openai-leavitt-unit-nonsofic`.
- Property FA: `R^x` is a homomorphic image of a hyperbolic Kazhdan group
  (`hyperbolic-kazhdan-cover-of-leavitt-unit-group`), and property (T) passes to
  quotients, so `R^x` has property (T); then `property-t-implies-property-fa`
  gives property FA.

The consequence for the host census is
`leavitt-tower-outside-sofic-permanence-closure`: `R^x`, and every group
containing it, lies outside the closure of the sofic groups under the permanence
operations, so no permanence argument starting from sofic groups can prove its
surjunctivity.
