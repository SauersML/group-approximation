---
rg: 2
id: enumerated-presentation-finite-generation-levels
kind: claim
title: On enumerated presentations finite generation, finiteness and property (T) are all Sigma-zero-three complete, driven by the finite-generation quantifier
distinct_from:
  kazhdan-property-t-of-finite-presentations-is-sigma1-complete: that classifies (T) where the group is known to be finitely generated, at level one; this shows that on countably generated syntax the level jumps to three, and that the jump is entirely the cost of certifying finite generation.
  residual-finiteness-of-enumerated-presentations-is-pi3-complete: that is a Pi-zero-three statement whose third quantifier is genuinely about finite quotients; this is a Sigma-zero-three statement whose third quantifier is only about a cofinite set of generators being redundant.
---

ESTABLISHED.  For countably generated enumerated presentation codes,

```text
FG_enum      (the group is finitely generated)   is Sigma^0_3-complete,
FINITE_enum  (the group is finite)               is Sigma^0_3-complete,
T_enum       (the group has property (T))        is Sigma^0_3-complete,
FP_enum      (the group is finitely presentable)  is Sigma^0_3-complete.   (EG1)
```

Contrast: `TRIVIAL_enum` is `Pi^0_2`-complete, `FP_rec2` is only known to be
`Sigma^0_2`-hard ([[finite-presentability-two-generator-recursive-is-sigma2-hard]]), and, on finitely generated
syntax, finiteness and (T) are `Sigma^0_1`-complete.  The extra levels on
enumerated syntax come from the quantifier "all but finitely many
generators are redundant", which is `Sigma^0_3` and is exactly the shape
of the cofiniteness index set `COF`.
