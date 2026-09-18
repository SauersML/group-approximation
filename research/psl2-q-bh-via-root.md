---
rg: 2
id: psl2-q-bh-via-root
kind: route
title: PSL_2(Q) sits in PGL_2(Q), which embeds in GL_4(Q), so the root gives PSL_2(Q)
target: psl2-q-embeds-in-fp-simple-group
requires:
  - gl-n-q-embeds-in-fp-simple-group
  - gl-n-q-targets-are-cofinal-in-n
---

`PSL_2(Q) <= PGL_2(Q)`. `gl-n-q-targets-are-cofinal-in-n` embeds `PGL_2(Q)` in
`GL_4(Q)` by the conjugation action on `M_2(Q)`. The case `n = 4` of
`gl-n-q-embeds-in-fp-simple-group` embeds `GL_4(Q)` in a finitely presented
simple group. Composing gives the target. The adjoint action on trace-zero
matrices would use the case `n = 3` instead.
