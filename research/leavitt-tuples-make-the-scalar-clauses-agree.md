---
rg: 2
id: leavitt-tuples-make-the-scalar-clauses-agree
kind: claim
title: In a ring with a Leavitt (1,d)-tuple, refinement carries λI_N to λI_(N+d-1) inside the elementary groups, so every stably trivial rational scalar is elementary at every rank N >= 3 and the stable and unstable K_1 clauses of the ring gate agree
distinct_from:
  ring-gate-k1-clause-is-unstable: that separates the stable clause (ker(Q^x -> K_1) f.g.) from the necessary unstable clause (Λ_N f.g.) and opens loophole (i); this closes loophole (i) for every ring containing a Leavitt (1,d)-tuple.
  leavitt-refinement-identifies-unstable-k2-levels: that uses Voronetsky refinement for Steinberg groups and K_2; this uses it for elementary groups and scalars.
---

**ESTABLISHED** through `leavitt-tuples-make-the-scalar-clauses-agree-proof`. Lane proof, not independently reviewed.
It is elementary given Voronetsky refinement (arXiv:2004.08551v2, §4, Prop. 1, read at source by gq-referee-b, report
dcf202f7c). No priority is claimed.

**Setting.** `R` is a unital ring with a unital map `Q -> R` and a Leavitt `(1, d)`-tuple, `d >= 2`: isometries
`σ_1, ..., σ_d` with `σ_i* σ_k = δ_(ik)` and `Σ_i σ_i σ_i* = 1`. Let `ι : Q^x -> K_1(R)` be the induced map, and
`Λ_N(R) = {λ : λ I_N in E_N(R)}`.

**Statement.**
1. **Refinement of elementary groups.** For `N >= 3`, the ring isomorphism `α : M_N(R) -> M_(N+d-1)(R)`, which splits the
   last coordinate by the `σ_i`, maps `E_N(R)` onto `E_(N+d-1)(R)` and `λ I_N` to `λ I_(N+d-1)`. So
   `Λ_N(R) = Λ_(N+d-1)(R)`.
2. **Stable scalars are elementary at every rank.** `ker ι ⊆ Λ_N(R)` for every `N >= 3`. Together with
   `Λ_N(R)^N ⊆ ker ι` (`ring-gate-k1-clause-is-unstable`, item 2), `ker ι` is finitely generated if and only if
   `Λ_N(R)` is.
3. **Loophole (i) is empty here.** No frame design containing a Leavitt `(1, d)`-tuple lies in loophole (i) of
   `frame-designs-for-the-ring-gate-are-bracketed`. For these designs the `K_1` branches of items 2--7 exclude hosts, not
   only designs that declare the stable clause. This covers every design of integer index `d >= 2` with `t s = I_d`, for
   example `R_L`, where `Λ_N(R_L) = Q^x` by item 2, since `ker ι = Q^x`.
4. **Where (i) can still live.** In rings without any Leavitt tuple. Since `(d - 1)[1] = 0` whenever a Leavitt
   `(1, d)`-tuple exists, these include every ring in which `[1]` has infinite order. So loophole (i) concerns exactly
   the index-`1` graded designs, the fractional-index frames with `t s != I_d`, and non-frame designs.
