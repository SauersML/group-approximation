---
rg: 2
id: fp-simple-nonsofic-via-leavitt-unit-group
kind: route
title: The binary Leavitt unit group is finitely presented, simple and nonsofic
target: fp-simple-nonsofic-group
requires: [leavitt-unit-group-finitely-presented, binary-leavitt-unit-group-is-simple, openai-leavitt-unit-nonsofic]
artifacts:
  - research/artifacts/khanh-2609-08428-leavitt-gl-verified-2026-09-11.md
---

Take `K = L_(F_2)(1,2)^x`.

- `K` is finitely presented: `leavitt-unit-group-finitely-presented`, imported
  from Khanh arXiv:2609.08428v1, Theorem 6.1.
- `K` is simple: `binary-leavitt-unit-group-is-simple` (the three-leaf prefix code
  identifies `K` with `GL_3(L) = EL_3(L)`, which is simple).
- `K` is not sofic: `openai-leavitt-unit-nonsofic` (Theorem 1.1 of the OpenAI
  chapter, also independently kernel-checked here).

So `K` is a finitely presented simple nonsofic group. This supersedes Attempt 1
recorded on the target ("no finite presentation of any `EL_n(L_(F_2)(1,2))` is
known here"). The finite-presentation input is a v1 preprint whose proof has not
been reviewed in this repository; see the artifact.
