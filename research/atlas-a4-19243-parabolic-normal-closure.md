---
rg: 2
id: atlas-a4-19243-parabolic-normal-closure
kind: claim
title: Inside the affine parabolic, collision 19243 normally kills only the translation radical
artifacts:
  - experiments/atlas_a4_19243_normal_closure.py
---

Use the subgroup ladder of `atlas-a4-19243-parabolic-subgroup-ladder`:

```text
H = diag(GL_3(F2),1),                  |H|=168,
P = <H,b> ~= AGL_3(F2),                |P|=1344,
```

where `b` is the repeated first-chart involution occurring in collision
`q_19243`.  Let `V` be the order-eight translation radical of `P`.
Then

```text
<<b>>_P = V ~= (C2)^3,                                 (19243-P-NC)
P / <<b>>_P ~= GL_3(F2) ~= H.                          (19243-P-QUOT)
```

In particular, any argument which compiles the fourteen-word rank-three core
and collision `19243` only into a representation of the affine parabolic can
at best kill the translation sector.  A full `GL_3(2)` quotient remains and
can still carry arbitrary multiplicity holonomy.

By contrast the same element `b`, viewed in the full chart group
`A8 ~= GL_4(F2)`, has normal closure all of `A8`.  The exact audit records

```text
|Conj_H(b)|=7,
|<<b>>_P|=8,
|P/<<b>>_P|=168,
|Conj_A8(b)|=105,
|<<b>>_A8|=20160.
```

Thus the central `C3` packet directions outside `P`, or some equivalent
full-chart consequence, are not cosmetic: they are exactly what upgrades the
collision from killing a translation radical to killing every nontrivial
holonomy sector.

## Attempts

- In the standard affine matrix model, check directly that `b` is a nonzero
  translation.  `H=GL_3(2)` acts transitively on the seven nonzero translation
  vectors, so its conjugates generate all of `V` and nothing outside `V`.
  The full-chart statement should follow from simplicity of `A8`, with the
  exact script serving as an independent finite audit.
