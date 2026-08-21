---
rg: 2
id: uniform-centralizer-filling-finiteness-proof
kind: route
title: Apply proper twisted-Schreier area to the whole stabilizer
target: bounded-centralizer-fillings-force-finite-stabilizer
requires:
  - finite-mark-centralizer-commutator-area-is-proper
---

Let `K=<b>`.  The quantitative estimate `(FMC1)` gives constants `A>0` and
`B>=0`, independent of `h` and its representing word, such that

```text
Area_R([beta,eta_h]) >= A d_(K\G)(K,Kh)-B.             (UCP1)
```

If `(UCF2)` holds, all cosets `Kh`, `h in H`, lie in one bounded ball of the
right Schreier graph.  The graph is locally finite because `X` is finite, so
that ball contains only finitely many cosets.  Hence the image of `H` in
`K\G` is finite.  Every fiber has at most `|K|` elements: if `Kh=Kh'`, then
`h'h^(-1) in K`.  Since `K` is finite, `H` is finite.

Conversely, if `H` is finite, choose one word `eta_h` for each of its finitely
many elements and one van Kampen diagram for each null word
`[beta,eta_h]`.  The maximum of their finitely many areas gives `(UCF2)`.

If `H` is infinite, its set of cosets `Kh` is infinite by the same finite-fiber
argument.  Local finiteness makes their distances from `K` unbounded, and
`(UCP1)` proves `(UCF3)` for every word section.

Finally, `SL_3(Z)` is infinite and has property `(T)`; the Carter--Keller
bounded-generation theorem gives bounded generation by its finitely many
elementary root subgroups.  It centralizes the finite mark in `(UCF4)`, so
the preceding argument applies without using or contradicting either of
those two properties.

The bounded-generation input is David Carter and Gordon Keller, *Bounded
elementary generation of `SL_n(O)`*, American Journal of Mathematics 105
(1983), 673--687, applied to `O=Z` and `n=3`.
