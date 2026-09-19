---
rg: 2
id: division-ring-hosts-no-binary-leavitt-family
kind: claim
title: No division ring hosts a binary Leavitt family
distinct_from:
  augmentation-blocks-unital-leavitt-family: that rules out Leavitt families in rings admitting a unital map to Z, and in every M_n(ZG), by an augmentation argument that never uses the idempotent relation; this rules them out in division rings, where the orthogonality relations force both s_i t_i = 1 and the idempotent relation then reads 1 + 1 = 1. Different hypothesis, different mechanism, disjoint targets.
  leavitt-gl-equals-el-and-perfect-unit-group: that is the internal algebra of the Leavitt algebra itself; this says where those relations can never be realized.
artifacts:
  - research/artifacts/strong-atiyah-audit-2026-08-17.md
---

A nonzero division ring `D` contains no binary Leavitt family: there are no
`s_0, s_1, t_0, t_1` in `D` with

    t_i s_j = delta_{ij},        s_0 t_0 + s_1 t_1 = 1.

One line: `t_i s_i = 1` in a division ring makes `s_i` and `t_i` mutually
inverse, so `s_i t_i = 1` for **both** `i`, and the idempotent relation
becomes `1 + 1 = 1`, i.e. `1 = 0`.

## Why it is worth a node

It closes the Leavitt lane in the skew-field direction, exactly as
`augmentation-blocks-unital-leavitt-family` closes it in the integral
group-ring direction, and the two mechanisms are complementary: the
augmentation argument uses only the orthogonality relations and never the
idempotent one, while here the orthogonality relations are what collapse the
two `s_i t_i` and the idempotent relation is what breaks.

Consequence for the property-`(TT)` development: its ring hypotheses are
intrinsically unavailable in a Linnell skew field.  Note also that
`HasSingleSandwichDivision` (every nonzero `a` admits `x a y = 1`) is **not**
skew-field control -- it holds in division rings and equally in unital purely
infinite simple rings, which is what the file's own docstring says it is for.
So neither the Leavitt relations nor the sandwich hypothesis can be used to
reach a statement about division rings of group algebras.
