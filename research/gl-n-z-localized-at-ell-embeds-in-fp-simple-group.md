---
rg: 2
id: gl-n-z-localized-at-ell-embeds-in-fp-simple-group
kind: claim
title: For a prime l and n >= 2, GL_n(Z_(l)) — hence every GL_n(Z[1/P]) with l not in P — embeds in a finitely presented simple group
distinct_from:
  gl-n-q-embeds-in-fp-simple-group: that root is GL_n(Q), which has no residually finite overgroup; this is the residually finite group obtained by leaving out one prime l, which contains GL_n(Z[1/P]) for every P missing l.
  rational-linear-groups-satisfy-boone-higman: that is Zaremsky's theorem for finitely generated subgroups of GL_n(Q), i.e. finite sets of primes; this is the non-finitely-generated group with all primes but one inverted.
---

**OPEN.** Let `l` be a prime and `n >= 2`. Then `GL_n(Z_(l))`, where
`Z_(l) = Z[1/q : q prime, q != l]`, embeds in a finitely presented simple group.

**Position.**
- **Which infinite P it covers.** Every `GL_n(Z[1/P])` with `l ∉ P` is a subgroup,
  so the claim for one `l` settles every set of primes that misses `l`. The
  claims for all `l` together settle every set `P` except the set of all primes.
- **Implied by the root.** `gl-n-q-embeds-in-fp-simple-group` implies it (route
  `gl-n-z-localized-via-gl-n-q`).
- **No converse by linear means.** `GL_n(Q)` embeds in no `GL_N(Z_(l))`
  (`z-localizations-embed-in-gl-n-only-along-inclusion`), and more generally in
  no residually finite group. The one known structural bridge back is the amalgam
  of `sl-2-q-is-an-amalgam-of-sl-2-z-localized-at-ell`, which needs more than
  this claim (`sl-2-z-localized-has-fp-hecke-overgroup`).
- **Easier than the root.** O1 does not apply: `GL_n(Z_(l))` is residually finite
  and self-similar (`aff-n-over-z-localized-at-ell-is-rf-and-self-similar`). O2
  (`SL_3(Z)` for `n >= 3`) and O4 (distorted unipotents) still apply.
- **Not reached by known theorems.** The group is not finitely generated. Its
  finitely generated overgroups are all non-linear
  (`infinite-prime-localizations-embed-in-no-fg-linear-group`), and its finitely
  generated affine self-similar subgroups see only finitely many primes.

## Attempts

- **Route through a finitely presented self-similar overgroup:**
  `gl-n-z-localized-via-fp-self-similar-overgroup`, OPEN via
  `aff-n-z-localized-lies-in-fp-self-similar-group`.
