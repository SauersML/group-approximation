---
rg: 2
id: finite-presentation-rice-criterion-via-the-fixed-positive-rope
kind: claim
title: A hereditary property is Pi-zero-two hard when the positive compiler family for a forbidden seed has it
artifacts:
  - research/artifacts/second-level-rice-theorem-2026-08-26.md
  - research/artifacts/mf-recognition-fp-pi2-completeness-2026-08-25.md
distinct_from:
  second-level-rice-theorem-for-local-approximation-properties: that reaches recursive presentations at the second level and finite presentations at the first; this reaches finite presentations at the second level from a property of the whole positive family for the chosen forbidden seed.
  mf-safe-finite-presentation-compiler: that is the compiler and the MF instance; this is the general criterion it yields once its positive branch is examined property by property.
  mf-recognition-finite-presentations-is-pi2-complete: that is the MF instance of the criterion.
---

Write R_e(d)=Carrier(P_e(d)) for the positive output of
[[mf-compiler-is-uniform-in-finite-seeds]], with finite seed code d.
The construction is jointly computable in d,e and satisfies

```text
e in INF  =>  Carrier(P_e(d)) = R_e(d),
e in FIN  =>  Carrier(d) embeds in Carrier(P_e(d)).                 (RC1)
```

**Criterion.**  Let `P` be a subgroup-hereditary, isomorphism-invariant
property of finitely presented groups. Suppose there is one finite
presentation code d such that

```text
(C1)  P(R_e(d)) for every e in INF,
(C2)  ¬P(Carrier(d)).
```

Then `P_fp` is `Pi^0_2`-hard and `NON-P_fp` is `Sigma^0_2`-hard.  If in
addition `P_fp` is `Pi^0_2`, then `P_fp` is `Pi^0_2`-complete.

**2026-09-20 correction.** Earlier wording identified all positive
outputs across seeds. That does not follow from the switch's trivial
abstract value: effective Higman sees a recursive presentation. Both
conditions above must concern the SAME seed. A sufficient replacement
for (C1) is the stronger uniform condition for every d and e in INF.
No seed-independence theorem is used.

**What the criterion explains.** Positive-family results give sufficient
tests for the cells of [[arithmetical-complexity-table-of-group-properties]];
these are not necessary for a different compiler to prove hardness:

```text
MF          yes  (the compiler's own theorem)   => complete
torsion-free yes ([[mf-compiler-positive-branch-is-torsion-free]]) => complete
sofic       open ([[sofic-safe-finite-presentation-compiler]])
hyperlinear open ([[mf-compiler-positive-branch-is-hyperlinear]])
LEF         NO ([[mikhailova-positive-rope-is-not-lef]]; equivalently RF on fp groups)
amenable    NO   (R_e contains free subgroups)
residually finite NO (R_e is not residually finite by construction)
```

So LEF, amenability and residual finiteness are not merely unproved by this
route: the route is *provably unavailable* for them, which is why their
completeness cells need a different mechanism
([[amenability-of-finite-presentations-is-pi2-complete]] and the
residually finite Higman problem).
