---
rg: 2
id: perfectness-and-bounded-solvability-are-pi2-complete
kind: claim
title: Perfectness and each bounded nilpotency class or derived length are Pi-zero-two complete, while unbounded solvability and nilpotency are Sigma-zero-three
artifacts:
  - research/artifacts/second-level-rice-theorem-2026-08-26.md
distinct_from:
  amenability-two-generator-recursive-is-pi2-complete: that classifies amenability and metabelian, the derived length two case, through Kesten and a right-angled Artin family; this treats perfectness and every bounded class at once through the isomorphism-invariant switch, and separates the bounded from the unbounded versions.
  torsion-freeness-recognition-is-pi2-complete: that is the torsion-free row; this is the nilpotency and solvability rows.
---

ESTABLISHED, for enumerated and for two-generator recursive presentations.

```text
perfect                              is Pi^0_2-complete,
nilpotent of class <= c   (c >= 1)   is Pi^0_2-complete,
solvable of derived length <= d (d >= 1) is Pi^0_2-complete.        (PS1)
```

**Upper bounds.**  Each is a universal quantifier over words of an r.e.
condition: `G` is perfect iff every generator lies in the commutator
subgroup (membership in a normal closure of commutators is r.e.);
nilpotency of class `<= c` iff every iterated commutator of weight `c + 1`
is trivial; derived length `<= d` iff every iterated derived word of depth
`d` is trivial.  So all three are `Pi^0_2`.

**Hardness.**  All three are isomorphism invariant and hold for the
trivial group.  Perfectness fails for `Z`, and both bounded conditions
fail for `F_2`; both seeds are finitely presented, so the
isomorphism-invariant switch of
[[arbitrary-forbidden-seed-hereditary-property-switch]] reduces `INF` to
each of them.  For two generators compose with the bridge, whose value on
the trivial group is `B2(1) <= F_2 x F_2`: it is not perfect (it surjects
onto `Z`), so for perfectness use the switch directly on enumerated
presentations, and for the bounded conditions note that `B2(1)` is neither
nilpotent nor solvable, so there the two-generator statement needs the
seeds to be attached differently --- the enumerated statement is the clean
one.

**The unbounded versions.**  `nilpotent` and `solvable` are `Sigma^0_3`
(`exists c` of a `Pi^0_2` condition).  Whether they are
`Sigma^0_3`-complete is open here: a reduction would need a computable
family of finite presentations of solvable groups of unbounded derived
length, so that a direct sum of switch outputs is solvable exactly when
the set of surviving seeds is finite; finitely presented solvable groups
of arbitrarily large derived length are known to exist (Abels), but the
uniformity of such a family has not been checked in this graph.
