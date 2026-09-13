---
rg: 2
id: bk-primitive-quotients-qd-or-traceless-proof
kind: route
title: Make the traceless interior a compact-free ideal, get the rest from dense quasidiagonal quotients, and glue
target: bk-primitive-quotients-qd-or-traceless-force-qd
requires:
  - bk-no-compact-open-ideals-are-qd-invisible
  - stw07-separating-qd-quotients-force-quasidiagonality
  - gabe-traceless-exact-qd-af-embedding
  - tww-gabe-schafhauser-af-embedding-theorem
artifacts:
  - research/artifacts/bk-t1-spectrum-simple-reduction-2026-09-12.md
---

Full proof in Sections 1--3 of the artifact.

Let `F` be the non-quasidiagonal primitive ideals, `V` the interior of `F`, and
`E_V` the ideal with `Prim(E_V) = V`.

1. **`E_V` is traceless.**  A trace with a finite nonzero value gives a
   hereditary `B ⊆ E_V` with a nonzero bounded trace (cut down to
   `her((a-ε)_+)`).  Krein--Milman gives an extreme tracial state `σ` of `B`,
   whose GNS closure is a factor.  So `σ` factors through `B/(B∩P)` for a
   primitive `P ∈ V`, which is hereditary in an ideal of the traceless `E/P'`.
   Stabilising by Brown's theorem and extending by `∞` off the generated ideal
   produces a nontrivial lower semicontinuous trace on `E/P'`, a contradiction.
2. **Compact-free.**  `E_V` is separable, exact, traceless, and stably finite as
   an ideal of `E`.  Gabe's Corollary C ((iii) ⟹ (iv)) says `Prim(E_V)` has no
   nonempty compact open subset.
3. **Quotient.**  `F \ V` has empty interior relative to `Prim(E) \ V`: an open
   `W` with `∅ != W \ V ⊆ F` would satisfy `W ⊆ F`, hence `W ⊆ V`.  So the
   quasidiagonal primitive quotients of `E/E_V` are dense in its spectrum, their
   kernels intersect in `0`, and `E/E_V` is quasidiagonal by the
   separating-quotients theorem.
4. **Glue.**  `bk-no-compact-open-ideals-are-qd-invisible` applies to
   `0 -> E_V -> E -> E/E_V -> 0`.

UCT consequence.  For a `T_1` spectrum, primitive quotients are simple.  A
simple exact algebra is stably finite iff it is not traceless (artifact Fact
T3).  A simple nuclear stably finite UCT algebra has a full corner with a
faithful bounded amenable trace, so it is quasidiagonal by
`tww-gabe-schafhauser-af-embedding-theorem`.  Hence every primitive quotient is
quasidiagonal or traceless.  For continuous fields with simple fibres,
`Prim(E) ≅ X`.
