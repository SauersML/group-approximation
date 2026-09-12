---
rg: 2
id: hyperbolic-groups-have-property-rd
kind: claim
title: Word hyperbolic groups have the Rapid Decay property
distinct_from:
  agkp-acylindrically-hyperbolic-rd-groups-selfless: that assumes rapid decay as a hypothesis for selflessness of reduced C*-algebras; this is the rapid decay theorem itself for word hyperbolic groups, used here to bound convolution operators on a quotient group.
artifacts:
  - research/artifacts/fpbs/docs/rd-weighted-fibre-bubble-criterion.md
---

**ESTABLISHED (citation).** Every finitely generated word hyperbolic group `Q`
has the Rapid Decay property for word length. There are constants `C` and `D`
such that for every `R` and every finitely supported `f` on `Q` supported on
elements of length at most `R`,

```text
||lambda_Q(f)||_{l2 -> l2}  <=  C R^D ||f||_2.
```

* **Credits:** Haagerup (Invent. Math. 50 (1979)) for free groups; Jolissaint
  (Trans. Amer. Math. Soc. 317 (1990)) for classical hyperbolic groups;
  de la Harpe (C. R. Acad. Sci. Paris Sér. I 307 (1988)) for Gromov hyperbolic
  groups.
* **Sources:** statement and credits as recorded in Chatterji, *Introduction to
  the Rapid Decay property*, arXiv:1604.06387 (Definition 1.1, RD(1), and the
  list of examples in Section 1). They were read from the arXiv LaTeX source on
  MSI. The primary papers were not re-read.
* **Other length functions:** RD for one word length gives it for every
  equivalent length (Chatterji, the remark after RD(3)).
* **Remaining radii:** for `R = 0` the inequality holds with constant `1`, so
  `(1+R)^D` may replace `R^D`.
