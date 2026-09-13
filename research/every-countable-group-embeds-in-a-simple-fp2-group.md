---
rg: 2
id: every-countable-group-embeds-in-a-simple-fp2-group
kind: claim
title: Every countable group embeds in a simple group of type FP_2
distinct_from:
  countable-group-embeds-in-two-generator-simple-group: that is the classical embedding into a finitely generated simple group with no finiteness condition beyond generation; this asks the simple envelope to be of type FP_2 over Z.
  boone-higman-conjecture: that asks for finitely presented simple envelopes of finitely generated groups with solvable word problem; this asks for FP_2 simple envelopes of arbitrary countable groups, including groups that are not recursively presented.
---

For every countable group `H` there is a simple group `Γ` of type `FP_2`
(over `Z`) and an injective homomorphism `H → Γ`.

This is the affirmative answer to Zaremsky Problem 1.25
(`zaremsky-1-25-countable-groups-embed-in-simple-fp2`), Question 1.12 of
Llosa Isenrich–Schesler–Wu arXiv:2510.01952v1.

## Attempts

- **Twisted Brin–Thompson envelopes (live).** By Fournier-Facio–Wu–Zaremsky
  arXiv:2603.24687v2, Corollary 4.14, an action `G ↷ S` of type `[HA_2]`
  (`G` of type `FP_2`, point stabilizers finitely generated, finitely many
  orbits of pairs) gives `SV_G` of type `FP_2`; if the action is faithful,
  `SV_G` is simple and contains `G`. So it suffices that every countable group
  lie in an `FP_2` group with a faithful `[HA_2]` action. Leary's `FP_2`
  overgroups (arXiv:1610.05813) come with no such action; the natural actions
  (regular, on cube complexes, imprimitive wreath actions over a regular base)
  all have infinitely many pair orbits. This is where the attempt stands.
- **Röver–Nekrashevych envelopes.** Llosa Isenrich–Schesler–Wu get simple groups
  with prescribed finiteness from self-similar linear groups. A faithful
  self-similar action on a rooted tree forces residual finiteness of the
  acting group, so arbitrary inputs must enter as subgroups of the envelope,
  not as the self-similar group itself. Not pursued yet.
