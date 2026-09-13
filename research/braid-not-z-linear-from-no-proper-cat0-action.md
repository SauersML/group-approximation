---
rg: 2
id: braid-not-z-linear-from-no-proper-cat0-action
kind: route
title: A braid group with no proper action on a proper CAT(0) space embeds in no GL_m(Z)
target: some-braid-group-embeds-in-no-glnz
requires:
  - some-braid-group-has-no-proper-cat0-action
  - number-field-linear-groups-act-properly-on-cat0-spaces
---

Suppose `B_N` admits no proper isometric action on any proper CAT(0) space. If
`B_N` embedded in some `GL_m(Z) <= GL_m(Q)`, then, being finitely generated,
it would act properly on the product of the symmetric space `GL_m(R)/O(m)`
with nothing else (`S` is empty for integer matrices). That space is proper
and CAT(0), a contradiction. So `B_N` embeds in no `GL_m(Z)`.
