---
rg: 2
id: sl-n-of-infinite-fields-lie-in-no-residually-finite-group
kind: claim
title: For every infinite field K and n >= 2, SL_n(K) has no nontrivial finite quotient, so GL_n(K) lies in no residually finite group
distinct_from:
  gl-n-q-embeds-in-fp-simple-group: that root's obstruction O1 excludes residually finite overgroups of GL_n(Q) through the divisible group (Q,+); this excludes them for GL_n(K) over every infinite field K, in every characteristic, through the simplicity of PSL_n(K), with no divisibility.
  sl-odd-q-simple-inputs-for-gl-n-q-root: that proves SL_m(Q) simple for odd m and uses it to replace the root's inputs by simple groups; this proves that SL_n(K) has no finite quotients over any infinite field and draws the consequence for residually finite overgroups.
---

**ESTABLISHED** by `sl-n-of-infinite-fields-no-rf-overgroup-proof` (classical
facts assembled; lane-proved, not independently reviewed; no novelty claimed).

## Statement

Let `K` be an infinite field and `n >= 2`.
1. The only finite quotient of `SL_n(K)` is the trivial group.
2. Consequently no group containing `SL_n(K)`, in particular `GL_n(K)`, is
   residually finite as an abstract group.

## Consequences for routes

- `GL_n(K)` embeds in no finitely generated linear group (Mal'cev), in no group
  acting faithfully on a locally finite rooted tree (hence in no self-similar
  group), and in no profinite group.
- **Characteristic p does not escape obstruction O1 of
  `gl-n-q-embeds-in-fp-simple-group`.** In characteristic `p` the additive
  group of `K` is not divisible, but the obstruction survives. So for
  `K = F_q(t)` every route through the repository's characteristic-`p` hosts
  (`char-p-linear-groups-satisfy-permutational-boone-higman`: finitely
  presented self-similar, hence residually finite, overgroups) can reach only
  finitely generated subgroups, never `GL_n(K)` itself.
- For `K = Q` this gives O1 a second time, independently of divisibility. It
  also covers `SL_n(Q)` and `PSL_n(Q)`, which have no divisible subgroup
  visible in the O1 argument once one passes to a quotient by unipotents.
- It is **not** an obstruction to the root question itself:
  `gl-n-over-algebraic-extensions-of-f-p-embed-in-v` gives infinite fields
  `K` (for example the algebraic closure of `F_p`) with `GL_n(K)` inside the
  finitely presented simple group `V`.

DERIVATION
sl-n-of-infinite-fields-no-rf-overgroup-proof
