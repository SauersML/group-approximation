---
rg: 2
id: zaremsky-3-10b-closed-mcg-in-some-out-fn-resolved
kind: claim
title: "Zaremsky Problem 3.10, second question with Out hosts, resolved: does every closed-surface MCG(S_g) embed in some Out(F_n)?"
distinct_from:
  zaremsky-3-10-out-fm-embeds-in-aut-fn: that is the whole of Problem 3.10 with three parts; this is the second question with hosts Out(F_n) only.
  zaremsky-3-10c-closed-mcg-in-some-aut-fn-resolved: that asks for hosts Aut(F_n); this asks for hosts Out(F_n), where a yes is implied by a yes there and nothing is known in the other direction.
---

Second question of Zaremsky Problem 3.10, "Does every MCG(Sg) embed in some
Out(Fn) and/or some Aut(Fn)?", with hosts `Out(F_n)`.

This claim is the question. It is established only through an answer route:

- **Yes**: `zaremsky-3-10b-by-yes` requires
  `every-closed-surface-mcg-embeds-in-some-out-free-group`.
- **No**: `zaremsky-3-10b-by-no` requires
  `some-closed-surface-mcg-embeds-in-no-out-free-group`.

Never write a `requires: []` route into this claim.

Known: yes for `g ≤ 2`. Any host has `n ≥ 2g − 1`.

## Attempts

- Recorded on the two answer claims.
