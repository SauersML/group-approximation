---
rg: 2
id: zaremsky-3-10c-closed-mcg-in-some-aut-fn-resolved
kind: claim
title: "Zaremsky Problem 3.10, second question with Aut hosts, resolved: does every closed-surface MCG(S_g) embed in some Aut(F_n)?"
distinct_from:
  zaremsky-3-10-out-fm-embeds-in-aut-fn: that is the whole of Problem 3.10 with three parts; this is the second question with hosts Aut(F_n) only.
---

Second question of Zaremsky Problem 3.10, "Does every MCG(Sg) embed in some
Out(Fn) and/or some Aut(Fn)?", with hosts `Aut(F_n)`.

This claim is the question. It is established only through an answer route:

- **Yes**: `zaremsky-3-10c-by-yes` requires
  `every-closed-surface-mcg-embeds-in-some-aut-free-group`.
- **No**: `zaremsky-3-10c-by-no` requires
  `some-closed-surface-mcg-embeds-in-no-aut-free-group`.

Never write a `requires: []` route into this claim.

Known: yes for `g ≤ 2`. Any host has `n ≥ 2g − 1`. The question depends only on
finite-index subgroups of `MCG(S_g)`
(`aut-free-embeddability-passes-to-finite-index-overgroups`).

## Attempts

- Recorded on the two answer claims.
