---
rg: 2
id: boone-higman-via-houghton-like-shift-envelopes
kind: route
title: Embed the input in a decidable finite presentation, pass to a Houghton-like envelope H_n(E_nu(P)) with n >= 2, and use Zaremsky's type (A) theorem for finitely presented strongly shift-similar groups
target: boone-higman-conjecture
requires:
  - clapham-fp-embedding-preserves-word-problem
  - mallery-zaremsky-shift-similar-envelope
  - houghton-like-groups-are-strongly-shift-similar
  - decidable-inputs-have-fp-houghton-like-shift-envelopes
  - fp-strongly-shift-similar-admits-type-a-action
  - type-a-action-gives-boone-higman-for-subgroups
---

Let `G_0` be finitely generated with solvable word problem.

1. By `clapham-fp-embedding-preserves-word-problem`, `G_0 <= P_0` with `P_0` finitely presented and with decidable
   word problem. Put `P = P_0 x Z`. As in `boone-higman-via-infinite-shift-compiler` step 2, `P` is infinite,
   finitely presented, has decidable word problem, and contains `P_0`.
2. By `decidable-inputs-have-fp-houghton-like-shift-envelopes` (OPEN), choose `nu` and `n >= 2` with
   `H := H_n(E_nu(P))` finitely presented.
3. `P <= E_nu(P)` (`mallery-zaremsky-shift-similar-envelope`), and `E_nu(P) <= H` by Observation 5.1
   (`houghton-like-groups-are-strongly-shift-similar` item 1). So `G_0 <= H`.
4. `H` is strongly shift-similar in some representation (item 2 there), and it is finitely presented. By
   `fp-strongly-shift-similar-admits-type-a-action`, it has a type (A) action.
5. By `type-a-action-gives-boone-higman-for-subgroups`, `G_0` embeds in a finitely presented simple group. ∎

**Relation to the other permutation route.** `boone-higman-via-infinite-shift-compiler` is the case `n = 1`, where
`H_1(E_nu(P)) = E_nu(P)`. For `n = 1` the germ gate needs the two-sided window
(`mz-envelope-fp-forces-two-sided-fg-near-index-kernel`), and generic enumerations fail it. For `n >= 2` the germ
gate is just "R_nu finitely presented", and generic enumerations pass it
(`houghton-like-envelopes-have-fp-germs-iff-fp-near-shift-group`).

*Correction, same day.* The first version said this route reduced Boone--Higman to one lifting statement for
generic `nu`. That lifting is false (`free-shift-houghton-like-envelopes-are-not-fp`): for free-shift enumerations
no `H_n(E_nu(P))` is finitely presented. So this route still needs an enumeration with near relations, which pin
`nu` down at infinity (item 3 there). This is the same kind of design problem as the other permutation and shell
routes. What this route still saves is the window conditions at the germ level.
