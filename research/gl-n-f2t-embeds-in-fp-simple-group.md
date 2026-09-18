---
rg: 2
id: gl-n-f2t-embeds-in-fp-simple-group
kind: claim
title: For every n >= 2 the group GL_n(F_2(t)) embeds in a finitely presented simple group
distinct_from:
  gl-n-q-embeds-in-fp-simple-group: that is the printed question for GL_n(Q); this is its function-field analogue over F_2(t), a stepping stone of this repository and not a printed question.
  positive-char-linear-groups-satisfy-boone-higman: that embeds every finitely generated linear group of positive characteristic; this asks for the whole countable group GL_n(F_2(t)), which is not finitely generated and lies in no residually finite group.
  char-two-laurent-linear-groups-satisfy-boone-higman: that embeds every subgroup of GL_n(F_q[t,t^-1]) in the Leavitt unit group; this needs all of F_2(t), that is, inverses of every nonzero polynomial.
---

**OPEN.** For every `n >= 2` there is a finitely presented simple group `S` and
an injective homomorphism `GL_n(F_2(t)) -> S`.

**Status as a question.** This is a stepping stone for
`gl-n-q-embeds-in-fp-simple-group`, posed in this repository. It is the
analogue over the rational function field, which, like `Q`, is the fraction
field of a principal ideal domain with infinitely many primes and finite
residue fields. The same question makes sense over `F_q(t)` for every `q`.

## Known

- **Finitely generated subgroups** embed in finitely presented simple groups
  (`positive-char-linear-groups-satisfy-boone-higman`).
- **Subgroups of `GL_n(F_2[t, t^-1])`**, not necessarily finitely generated,
  embed in the finitely presented simple group `L_(F_2)(1,2)^x`
  (`char-two-laurent-linear-groups-satisfy-boone-higman`, conditional on the
  imported finite presentation).
- **Conditional on Boone--Higman.** `F_2(t)` is a computable field, so
  `GL_n(F_2(t))` has solvable word problem for its standard enumeration.
  Survey arXiv:2306.16356v3, Corollary 3.5, then applies.

## Obstructions and non-obstructions for hosts

- **No residually finite overgroup**
  (`sl-n-of-infinite-fields-lie-in-no-residually-finite-group`). Every route
  through finitely presented self-similar or linear intermediate groups can
  reach only finitely generated subgroups.
- **n >= 3: neither V nor VA**
  (`char-p-transcendental-gl-n-avoids-v-and-va-for-n-ge-3`).
- **No distortion obstruction**
  (`char-p-linear-groups-have-no-distorted-cyclic-subgroups`). For `n = 2`,
  `V` and `VA` are not excluded by any obstruction recorded here. By contrast
  O4 excludes `VA` for `GL_2(Q)`.

## Routes

1. `gl-n-f2t-bh-via-leavitt-field`: if `F_2(t)` is a unital subring of the binary
   Leavitt algebra (`rational-function-field-embeds-in-binary-leavitt-algebra`),
   then every subgroup of every `GL_n(F_2(t))` lies in `L_(F_2)(1,2)^x`.

2. `gl-n-f2t-bh-via-horner-resolvent-leavitt-tensor` (2026-09-18, lane `bh-algebra`): `F_2(t)` lies in the
   explicit finitely presented central simple algebra `R_2` of
   `char-p-rational-function-field-in-fp-simple-algebra` (lane proof), so every
   `GL_n(F_2(t))`, all `n` at once, lies in `(R_2 ⊗ L)^x`. That group is finitely presented and simple
   once `K_1(R_2 ⊗ L) = K_2(R_2 ⊗ L) = 0` (`horner-resolvent-leavitt-tensor-k1-k2-vanish`, OPEN). This
   replaces the embedding into the fixed algebra `L_(F_2)(1,2)` by a `K`-theory computation.

## Attempts

- **Transfer to Q** (2026-09-17, lane `gq-countable-fields`). See
  `research/artifacts/gq-gq-countable-fields-transfer.md`.
