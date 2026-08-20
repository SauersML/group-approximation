---
rg: 2
id: chornomaz-wagner-quasilinear-s-machine-emulation
kind: claim
title: A Turing machine is emulated by an S-machine in quasilinear time
artifacts:
  - research/artifacts/two-paper-ingestion-2026-08-19.md
distinct_from:
  word-problem-of-finite-presentation-is-re: that is the recursive-enumerability of the word problem of a finite presentation; this is a complexity-preserving machine simulation and says nothing about decidability.
  markov-post-undecidable-monoid-word-problem: that is undecidability of a monoid word problem; this concerns the time and space cost of emulating a computation and presupposes decidability downstream.
---

**Established by citation.**  Chornomaz--Wagner, arXiv:2304.07603v1,
`main-theorem` in `S_machine_arXiv.tex`:

> Let `M` be a multi-tape, non-deterministic Turing machine.  Then there exist
> `S`-machines which emulate `M` in quasilinear time: for all `eps>0` there is
> an `S`-machine `S_eps` with `L_(S_eps) = L_M` and time-space complexity
> `TMSP_(S_eps) <=_1 (TM_M^(1+eps), TM_M)`.

Complexity is measured up to the preorder `f <= g` iff `f(n) <= C g(Cn) + C`
for some `C`, and `<=_1` is the same relation applied to `max(f,n)`.

This replaces the bound implicit in Sapir--Birget--Rips Proposition 4.1, where
the emulating `S`-machine satisfies `TMSP <=_1 (TM_M^3, TM_M)` and, as the
source notes, that is an equivalence rather than merely an upper bound.  So the
time exponent drops from `3` to `1+eps`, and the *area* complexity -- the
product of the time and space bounds, which is what controls van Kampen diagram
area downstream -- drops from `T^4` to `T^(2+eps)`.

The route to the group-theoretic consequences is
`quantitative-higman-embedding-with-dehn-control`.  The technical vehicle is a
theory of `S`-graphs the source develops as, in its own words, "a crude
object-oriented programming language" for `S`-machines.
