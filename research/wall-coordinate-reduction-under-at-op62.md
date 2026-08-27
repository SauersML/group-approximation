---
rg: 2
id: wall-coordinate-reduction-under-at-op62
kind: claim
title: Under Alekseev--Thom Open Problem 6.2 the wall becomes a two-centralizer question
distinct_from:
  relative-wall-commutant-growth: That is the unconditional equivalence inside one target; this is a conditional transfer of it into matrix coordinates, whose hypothesis is a published open problem about Kazhdan representations into tracial matrix ultraproducts.
artifacts:
  - notes/TRUE_RELATIVE_WALL_IS_COMMUTANT_GROWTH.md
---

Alekseev--Thom, arXiv:2608.05362, Open Problem 6.2 asks whether the commutant
of a Kazhdan representation into a tracial matrix ultraproduct is the
ultraproduct of the coordinate centralizers of lifts.

**If** that description holds for a wall model, so that `N=prod^omega A_n`
and `N_t=prod^omega tilde A_n` with `A_n<=tilde A_n` the exact centralizers
in `M_(d_n)` of the lifted `Gamma`- and `Gamma_1`-windows, **then** the
trace-preserving expectations are the ultraproduct of the coordinate ones, so
`[N_t:N]<=lim_omega [tilde A_n:A_n]`, and a wall forces

```text
lim_omega [tilde A_n:A_n]>1.
```

So a positive answer to Open Problem 6.2 puts the wall entirely into finite
dimensions, as a demand on two nested exact centralizers.  Conversely,
without it neither the infinite-index corollary nor the Steinberg
cancellation has a coordinate form, because `N` may be strictly larger than
`prod^omega A_n`.

The implication is proved; the hypothesis is open and is not asserted.
