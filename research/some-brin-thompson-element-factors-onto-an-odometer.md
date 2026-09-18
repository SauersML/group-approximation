---
rg: 2
id: some-brin-thompson-element-factors-onto-an-odometer
kind: claim
title: For some k and m >= 2, some element of the Brin-Thompson group kV has the m-adic odometer as a topological factor
distinct_from:
  renormalizable-thompson-elements-are-odometer-codes: that proves every renormalizable element has such a factor; this asks whether any element of any kV has one at all.
  bs12-embeds-in-brin-thompson-2v: that asks for BS(1,2) in some nV; a negative answer here kills only the renormalization route to it, and a positive one does not give BS(1,2).
  three-v-contains-aperiodic-rationals: that uses a periodic-point-free SMART element of 2V; this asks whether some such element has continuous eigenvalues of unbounded order.
---

**OPEN.** There are `k >= 1`, `m >= 2`, `T ∈ kV` and a continuous surjection
`π: C^k -> Z_m` with `π ∘ T = π + 1`. Equivalently, for every `j` the space
`C^k` is split into `m^j` clopen sets that `T` permutes cyclically.

**Why it is a hole.** `renormalizable-thompson-elements-are-odometer-codes` proves
this is necessary for the renormalization route
(`renormalizable-thompson-elements-give-baumslag-solitar`) to
`bs12-embeds-in-brin-thompson-2v`. So a negative answer kills that route for
every `k` and `m`.

**Known constraints on a witness.**
- `T` has no periodic points, since `m^j` divides every period.
- This excludes the topological full group of the full shift, whose elements fix
  the constant configurations.
- Candidates must be periodic-point-free, such as SMART-type machines in `2V`
  (`three-v-contains-aperiodic-rationals`).

**Lead.** In Callard--Salo (arXiv:2208.00685v3) the level moves of SMART take
`f(k+1) = 3 f(k) + 4` steps. A SMART-type machine with exact tripling
`f(k+1) = 3 f(k)` is the natural candidate both for this claim and for a height-3
renormalization. Whether SMART itself has continuous eigenvalues was not
checked.
