---
rg: 2
id: simple-fa-input-boone-higman
kind: claim
title: Every finitely generated simple group with property FA and solvable word problem embeds in a finitely presented simple group
distinct_from:
  infinite-simple-input-boone-higman: that asks for finitely presented simple envelopes of all infinite computably presented simple inputs, which may split as amalgams; this asks only for inputs with property FA, which do not split.
  boone-higman-conjecture: that quantifies over all finitely generated groups with solvable word problem; this restricts to simple inputs with property FA, and it is equivalent to the conjecture only if decidable-groups-embed-in-decidable-simple-fa-groups holds.
---

**OPEN.** Let `S` be a finitely generated simple group with property FA and
solvable word problem. Then there is a finitely presented simple group `H` and
an embedding `S <= H`.

This is a special case of `boone-higman-conjecture`. The route
`boone-higman-from-simple-fa-inputs` shows the converse, conditional on
`decidable-groups-embed-in-decidable-simple-fa-groups`.

## Why this matters

Step 6 of `finitary-permanence-closures-collapse-proof` shows that every
closure operation, including arbitrary graphs of groups, carries a copy of a
finitely generated simple group with FA down into a base piece. So FA simple
inputs are the ones on which permanence reductions have no room, and a proof
for them must supply a genuinely new embedding. This claim isolates them as a
separate input class.

## Attempts

1. **Use FA as a finiteness property (2026-09-17).** Twisted Brin--Thompson
   hosts of the Belk--Zaremsky type are finitely presented only when the input
   and its point stabilizers have finiteness properties. Property FA says only
   that the input does not split. The decidable simple FA groups obtained from
   `lef-wp-groups-have-decidable-simple-kazhdan-lef-hosts` are Kazhdan and
   finitely generated, but nothing recorded makes them finitely presented. So
   FA gives the host no finiteness. *Dies* at finite presentation of the
   input. The finiteness criterion for twisted Brin--Thompson groups is recalled
   here as a locator and has not been re-read from source.
2. **Higman embedding first (2026-09-17).** A computably presented `S` embeds
   in a finitely presented group, but that group is not simple and may split.
   Passing to a simple quotient kills the embedding unless `S` avoids the
   kernel. *Dies* at the same place as the general conjecture: the FA
   hypothesis on `S` gives no control over the kernel of the quotient map.
