---
rg: 2
id: thompson-f-is-not-quasi-isometric-to-thompson-t
kind: claim
title: Thompson's group F is not quasi-isometric to Thompson's group T
distinct_from:
  thompson-f-is-quasi-isometric-to-thompson-t: that is the opposite answer to the same sub-question; this is the answer Zaremsky expects ("Surely not, but why not?").
---

**OPEN.** Thompson's group F with a word metric is not quasi-isometric to
Thompson's group T with a word metric. This is the no-answer to part (c) of
Zaremsky Problem 2.4 (`thompson-f-qi-to-thompson-t-resolved`).

## Attempts

- **Amenability.** If F is amenable, this follows from
  `amenability-is-a-quasi-isometry-invariant` and `thompson-t-is-not-amenable`:
  route `thompson-f-not-qi-to-t-if-f-is-amenable`. Where it stands: conditional on
  the open root `thompson-f-is-amenable`. An unconditional proof needs an invariant
  that does not collapse when F is non-amenable.
- **Coarse embeddings.** A proof that T admits no coarse embedding into F would
  suffice, since a quasi-isometry is one. Monotone invariants give no help so far:
  asymptotic dimension is infinite for both (F contains `Z^n` for every `n`), and
  non-amenability of T does not obstruct coarse embeddings into amenable groups.
  Where it stands: open.
- **Cohomology with group-ring coefficients.** `H^*(G; ZG)` is a quasi-isometry
  invariant among groups of type F_∞ (Gersten), F and T are both of type F_∞
  (Brown–Geoghegan; Brown), and `H^*(F; ZF) = 0` in every degree is reported by
  Brown–Geoghegan (Invent. Math. 77, 1984). A single nonzero `H^k(T; ZT)` would
  prove this claim. Where it stands: the three imports are not yet re-read from
  the sources; `H^*(T; ZT)` is not computed.
