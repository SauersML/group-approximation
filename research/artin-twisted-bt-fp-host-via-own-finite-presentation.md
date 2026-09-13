---
rg: 2
id: artin-twisted-bt-fp-host-via-own-finite-presentation
kind: route
title: "Dead: AV_A would be its own finitely presented host if it were finitely presented"
target: every-artin-twisted-brin-thompson-group-embeds-in-fp-group
requires:
  - every-artin-self-twisted-bt-group-is-finitely-presented
---

**Dead.** The implication is valid: a finitely presented group embeds in itself. Its
premise, `every-artin-self-twisted-bt-group-is-finitely-presented`, is refuted by
`self-twisted-bt-group-of-infinite-group-is-not-fp`, so this route never completes.

It records that the natural first attempt at Zaremsky Problem 3.8, proving that
`AV_A` itself is finitely presented through Zaremsky's criterion, fails for every
Artin group. The obstruction is the pair-orbit condition, not the finite presentation
of `A` or the point stabilizers, which are trivial.
