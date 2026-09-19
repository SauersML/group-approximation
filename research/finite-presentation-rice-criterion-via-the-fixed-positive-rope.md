---
rg: 2
id: finite-presentation-rice-criterion-via-the-fixed-positive-rope
kind: claim
title: A hereditary property is Pi-zero-two hard on finite presentations as soon as the compiler's positive rope has it
artifacts:
  - research/artifacts/second-level-rice-theorem-2026-08-26.md
  - research/artifacts/mf-recognition-fp-pi2-completeness-2026-08-25.md
distinct_from:
  second-level-rice-theorem-for-local-approximation-properties: that reaches only recursive presentations at the second level, and finite presentations at the first; this crosses to finite presentations at the second level, at the price of one hypothesis about a single explicit group.
  mf-safe-finite-presentation-compiler: that is the compiler and the MF instance; this is the general criterion it yields once its positive branch is examined property by property.
  mf-recognition-finite-presentations-is-pi2-complete: that is the MF instance of the criterion.
---

ESTABLISHED.  Write `R_e` for the compiler's positive-branch output
([[mf-safe-finite-presentation-compiler]]); on the `INF` branch the
construction is seed-independent, and the compiler is uniform in its
finitely presented seed `D`, giving a computable `e |-> P_e(D)` with

```text
e in INF  =>  Carrier(P_e(D)) = R_e,
e in FIN  =>  D embeds in Carrier(P_e(D)).                          (RC1)
```

**Criterion.**  Let `P` be a subgroup-hereditary, isomorphism-invariant
property of finitely presented groups such that

```text
(C1)  P(R_e) for every e in INF,
(C2)  ¬P(D) for some finitely presented D.
```

Then `P_fp` is `Pi^0_2`-hard and `NON-P_fp` is `Sigma^0_2`-hard.  If in
addition `P_fp` is `Pi^0_2`, then `P_fp` is `Pi^0_2`-complete.

**What the criterion explains.**  Each open finite-presentation cell of
[[arithmetical-complexity-table-of-group-properties]] is now the single
question "does the fixed rope `R_e` have the property":

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
