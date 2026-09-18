---
rg: 2
id: gl-n-over-algebraic-extensions-of-f-p-embed-in-v
kind: claim
title: For every algebraic extension K of a finite field, for example the algebraic closure of F_p, every GL_n(K) embeds in Thompson's group V
distinct_from:
  gl-n-q-embeds-in-fp-simple-group: that is the open question for K = Q; this settles the analogous question for the algebraic extensions of F_p, where GL_n(K) is locally finite, and serves as a calibration case.
  sl-n-of-infinite-fields-lie-in-no-residually-finite-group: that says GL_n(K) has no residually finite overgroup for infinite K; this exhibits infinite K for which GL_n(K) nevertheless lies in a finitely presented simple group, so that obstruction never excludes a finitely presented simple host.
---

**ESTABLISHED** by `gl-n-over-algebraic-extensions-of-f-p-in-v-proof` (an
immediate consequence of Higman's theorem; lane-proved, not independently
reviewed; no priority claimed).

## Statement

Let `K` be an algebraic extension of `F_p` and `n >= 1`. Then `GL_n(K)` embeds
in Thompson's group `V`, which is finitely presented and simple.

## Why it is recorded

It is the **calibration case** for the `GL_n(Q)` swarm.
- For infinite such `K`, for example the algebraic closure of `F_p`, the group
  `GL_n(K)` lies in no residually finite group
  (`sl-n-of-infinite-fields-lie-in-no-residually-finite-group`), yet it embeds
  in a finitely presented simple group.
- So "no residually finite overgroup" (obstruction O1 of
  `gl-n-q-embeds-in-fp-simple-group`) only excludes residually finite
  intermediate groups. Any argument claiming that O1-type facts prevent a
  finitely presented simple host for `GL_n(Q)` also "proves" that `GL_n(F_p-bar)`
  has none, which is false.
- What `GL_n(Q)` has and these groups lack is an element of infinite order:
  these groups are locally finite.

DERIVATION
gl-n-over-algebraic-extensions-of-f-p-in-v-proof
