---
rg: 2
id: gl-n-qbar-embeds-in-fp-simple-group
kind: claim
title: For every n >= 2, GL_n of the algebraic numbers embeds in a finitely presented simple group
distinct_from:
  gl-n-q-embeds-in-fp-simple-group: that is GL_n(Q); this is GL_n(Qbar), which lies in no GL_N or GL_infinity over a number field (prufer-groups-do-not-embed-in-gl-infinity-q), so the root does not imply it by restriction.
  number-field-gl-n-embeds-in-fp-simple-group: that is GL_n(K) for number fields K, equivalent to the root; this is the algebraic closure.
  countable-char-zero-linear-groups-embed-in-fp-simple-groups: that is every countable characteristic-0 linear group, which implies this claim.
artifacts:
  - research/artifacts/gq-gq-transfer-consequences.md
---

**OPEN.** For every `n >= 2`, the countable group `GL_n(Qbar)` embeds in a
finitely presented simple group.

- **n = 1 is known.** `Qbar^x` is countable abelian, so it embeds in `VA`
  (Belk–Hyde–Matucci; BBMZ survey Theorem 4.11).
- **Not implied by restriction.** `GL_n(Qbar)` contains `Z(p^∞)`, so it lies in
  no `GL_∞(K)` over a number field `K`
  (`prufer-groups-do-not-embed-in-gl-infinity-q`). Neither
  `gl-n-q-embeds-in-fp-simple-group` nor `gl-infinity-q-embeds-in-fp-simple-group`
  implies this claim through a linear embedding. A host must contain divisible
  torsion. `Q/Z` embeds in `V`, so this is no obstruction to a Thompson-type
  host.
- **Implied** by `countable-char-zero-linear-groups-embed-in-fp-simple-groups`
  (route `gl-n-qbar-via-countable-char-zero-linear-groups`), and by the
  Boone–Higman conjecture through survey Corollary 3.5.

No printed source asks this form; it is recorded as a transfer target.

## Attempts

None.
