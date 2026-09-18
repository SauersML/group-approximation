---
rg: 2
id: every-countable-group-embeds-in-simple-fp2-via-fp2-shells
kind: route
title: Put the countable group in a perfect finitely generated group and make its shell envelope FP_2; perfect inputs make shell envelopes simple
target: every-countable-group-embeds-in-a-simple-fp2-group
requires:
  - every-countable-group-has-an-fp2-shell-envelope
  - perfect-input-shell-envelopes-are-simple
---

Let `H` be countable. By `every-countable-group-has-an-fp2-shell-envelope` there are a finitely
generated perfect `P ≥ H` and an enumeration `ν` with `E_ν = ⟨V, hat(P)⟩` of type `FP_2`. The map
`hat` embeds `P` in `E_ν` (`shell-cantor-embeddings-are-finite-germ-extensions`), and `E_ν` is
simple because `P` is perfect (`perfect-input-shell-envelopes-are-simple`). So `H ≤ P ≤ E_ν`,
a simple group of type `FP_2`.

This route differs from `every-countable-group-embeds-in-simple-fp2-via-ha2-actors`: it needs no
faithful action with finitely many orbits of pairs and no twisted Brin–Thompson group. Its only open
premise is homological finiteness of one explicit finite germ extension of `V`. By
`bhm-singfix-finiteness-holds-for-type-fp-n`, that reduces to the one-point and two-point
`SingFix` groups. The Boone–Higman shell route asks the same question with `F_2` in place of `FP_2`,
a decidable finitely presented input, and a computable enumeration.
