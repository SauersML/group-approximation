---
rg: 2
id: number-field-linear-groups-embed-in-gl-n-q
kind: claim
title: For a number field K of degree d, restriction of scalars embeds GL_n(K) in GL_nd(Q)
distinct_from:
  algebraic-linear-groups-satisfy-boone-higman: that uses restriction of scalars for finitely generated linear groups over number fields; this records the embedding of the whole countable group GL_n(K) into GL_nd(Q), for transfer from gl-n-q-embeds-in-fp-simple-group.
  gl-n-q-targets-are-cofinal-in-n: that compares GL_n(Q), SL_n(Q) and PGL_n(Q) over Q; this passes from number fields to Q.
artifacts:
  - research/artifacts/gq-gq-transfer-consequences.md
---

**ESTABLISHED** by `number-field-linear-groups-embed-in-gl-n-q-proof`
(elementary; not independently reviewed; no novelty claimed).

**Statement.** Let `K` be a number field with `[K:Q] = d` and let `n >= 1`. Then
`GL_n(K)` embeds in `GL_(nd)(Q)`. Consequently, for any property `P` of groups
inherited by subgroups, `P(GL_N(Q))` for every `N` implies `P(GL_n(K))` for
every number field `K` and every `n`.

**Proof.** Fix a `Q`-basis of `K`, so `K^n ≅ Q^(nd)` as `Q`-vector spaces. Each
`g in GL_n(K)` acts `K`-linearly, hence `Q`-linearly and bijectively, on `K^n`.
This gives a homomorphism `GL_n(K) -> GL_Q(K^n) ≅ GL_(nd)(Q)`. It is injective
because the action of `GL_n(K)` on `K^n` is faithful.
