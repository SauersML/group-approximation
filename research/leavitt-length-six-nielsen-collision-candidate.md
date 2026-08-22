---
rg: 2
id: leavitt-length-six-nielsen-collision-candidate
kind: claim
title: A minimal packet move gives a full-support length-six word with an exact Nielsen gate collision
artifacts:
  - research/leavitt-length-six-nielsen-collision-candidate-proof.md
  - research/artifacts/verify-leavitt-length-six-nielsen-collision.py
distinct_from:
  leavitt-length-six-three-gate-weight-survivor: that word defeats the weight test but its two Nielsen maps are injective; this moves the q packet and makes the first Nielsen map have an explicit kernel word.
  leavitt-three-gate-candidate-is-injective: that proves injectivity from two Nielsen embeddings; the first of those two embeddings fails here because two formal gates have the same Leavitt image.
  kl-violating-equation-over-leavitt-unit-group: that asks for an actual equation with no solution over any extension; this is a rigorously screened next candidate, not yet a KL violation.
---

Let

```text
a=x_12(s_0),  e=x_12(t_1),  p=(1 2 ... 20),
q=x_34(s_1)x_(11,12)(t_0)
```

in `G=EL_20(L_(F_2)(1,2))`, and consider

```text
W_col=a t^2 a t p t e t^(-1)q t^(-1).               (NC1)
```

Its nonidentity coefficients are exactly the same full generating set
`{a,q,p,e}` as in the fenced three-gate word.  Its `t`-length is six, its
degree is two, and the two cyclic sign-change coefficients remain the
involutions `a,e`.

In the paired degree-two rewrite, the two formal copy-one gate labels are
both `a_1`.  Thus the natural local-atlas map has the explicit nontrivial
kernel word `k_0k_1`.  The modification is minimal among packet changes with
`a,p,e` fixed: equality of those gates forces the middle slot to change from
`q` to `a`, and preservation of full support forces `q` into the idle final
slot.

This is the next explicit Leavitt KL candidate selected by a deliberate
Nielsen-table collision.  The collision invalidates the complete
Nielsen--amalgam fence for the previous word, but it does not yet establish a
coefficient-copy kernel in the full paired quotient.
