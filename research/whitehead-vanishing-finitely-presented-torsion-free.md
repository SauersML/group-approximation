---
rg: 2
id: whitehead-vanishing-finitely-presented-torsion-free
kind: claim
title: Whitehead vanishing for finitely presented torsion-free groups
distinct_from:
  whitehead-vanishing-recursively-presented-torsion-free: that drops finite presentation; the two are now equivalent through the established Whitehead-injective Higman embedding.
  whitehead-vanishing-torsion-free: that is the global conjecture; the two are now equivalent through the established recursively-presented reduction and Whitehead-injective embedding.
  whitehead-universal-finitely-presented-torsion-free-group: that established theorem constructs one finitely presented torsion-free tester; this open claim is equivalent to the assertion that the tester's Whitehead group vanishes.
  whitehead-vanishing-universal-test-group: that concentrates the global statement into an explicit uncountable restricted product; this node quantifies over finitely presented groups, although the new finite tester concentrates it further.
  hnn-torsion-theorem: that is a torsion permanence theorem for HNN extensions; this is an algebraic K-theory vanishing statement.
  torsion-free-finitely-presented-non-mf: that asks for one non-MF group in the same input class; approximation and Whitehead vanishing remain logically unrelated.
artifacts:
  - research/artifacts/whitehead-vanishing-audit-2026-08-17.md
---

Wh(H)=0 for every finitely presented torsion-free group H.

**OPEN.** What changed on 2026-08-30 is the reduction, not the vanishing:
[[whitehead-injective-torsion-free-embedding]] is now established, so this
claim implies the recursively presented case and hence the global torsion-free
Whitehead conjecture. The reverse implication is immediate. Thus this node is
now exactly equivalent to [[whitehead-vanishing-torsion-free]].

There is also one finitely presented torsion-free group U from
[[whitehead-universal-finitely-presented-torsion-free-group]] such that this
claim is equivalent to the single computation Wh(U)=0. Every finitely
presented torsion-free G maps Whitehead-injectively into U.

## What remains

The transfer obstruction is gone. The remaining issue is genuine vanishing:
prove Wh(U)=0, equivalently prove the degree-one Farrell--Jones assembly map
surjective for U, or exhibit a nonzero Whitehead class in some finitely
presented torsion-free group.

A presentation-splitting induction still does not cover arbitrary finitely
presented groups, and Waldhausen sequences can contain Nil terms. Most named
families lie in the Farrell--Jones class, but no theorem covers all finitely
presented torsion-free groups and no counterexample with nonzero Wh is known.
