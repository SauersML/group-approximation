---
rg: 2
id: z-localizations-embed-in-gl-n-only-along-inclusion
kind: claim
title: Z[1/P] embeds in some GL_N(Z[1/P']) only if P is contained in P', so GL_n(Z[1/P]) embeds in GL_N(Z[1/P']) exactly when P ⊆ P'
distinct_from:
  infinite-prime-localizations-embed-in-no-fg-linear-group: that excludes finitely generated linear overgroups; this compares the non-finitely-generated groups GL_n(Z[1/P]) with each other.
  gl-n-q-embeds-in-fp-simple-group: that root's obstruction O1 shows GL_n(Q) is in no residually finite group; this is the sharper linear statement that no GL_N(Z[1/P']) with P' missing a prime contains even (Q,+), and more generally that divisibility at a prime cannot be traded for divisibility at other primes inside GL_N of a localization.
---

**ESTABLISHED** through `z-localizations-embed-in-gl-n-only-along-inclusion-proof`.
Lane proof, not independently reviewed. No priority is claimed.

**Statement.** Let `P, P'` be sets of primes and `N >= 1`. If the additive group
`Z[1/P]` embeds (as an abstract group) in `GL_N(Z[1/P'])`, then `P ⊆ P'`.
Consequently, for `n >= 2`:
`GL_n(Z[1/P])` embeds in `GL_N(Z[1/P'])` for some `N` if and only if `P ⊆ P'`.

**Reading for the root.**
- Taking `P` = all primes: `GL_n(Q)`, and even `(Q,+)`, embeds in no
  `GL_N(Z[1/P'])` with `P'` missing a prime.
- The groups `GL_n(Z[1/P])` form a lattice indexed by the sets of primes, and
  linear embeddings between them only go along inclusion.
- So no linear trick can reduce the case of all primes, or of an infinite `P`,
  to a smaller `P'`. Any reduction of `gl-n-q-embeds-in-fp-simple-group` to the
  residually finite groups `GL_n(Z[1/P'])` must pass through a non-linear,
  non-residually-finite construction. One such construction is the amalgam of
  `sl-2-q-is-an-amalgam-of-sl-2-z-localized-at-ell`.
