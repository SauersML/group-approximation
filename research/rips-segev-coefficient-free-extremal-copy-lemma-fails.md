---
rg: 2
id: rips-segev-coefficient-free-extremal-copy-lemma-fails
kind: claim
title: In Steenbock's Rips--Segev core there are finite port-closed supports S_X = S_Y b with a minimal covering by copies of g(Gamma) in which every copy meets the union of the others in at least nine cosets, so no support-only extremal-copy lemma with threshold at most eight can drive an induction on the number of copies
distinct_from:
  rips-segev-three-copy-configurations-carry-no-zero-divisors: that proposes the extremal-copy step (threshold three) as the route to every N; this shows the step is false when read on supports alone, for every threshold up to eight.
  rips-segev-six-copy-configurations-carry-no-zero-divisors: that is a positive fixed-N result (N <= 6) from shell counting and the rank-one lemma; this is an obstruction to the induction on N that would extend it.
  rips-segev-groups-satisfy-kaplansky-zero-divisor: that is the open question; this rules out one proposed route to its b-degree-one case, not the question itself.
---

**ESTABLISHED (proposed; unreviewed), obstruction.**  Derivation:
`rips-segev-coefficient-free-extremal-copy-lemma-fails-proof`.

**Setting.**  As in `rips-segev-three-copy-configurations-carry-no-zero-divisors`: `Gamma` is Steenbock's graph
with `Gr'_*(1/8)` and `gamma >= 42`, `K` is its core, and a *copy* is `h g(Gamma)`, `h in K`.  A *link* between a
copy and a set of copies is an `<a>`-coset meeting both, or a bridge.

**Theorem.**  For every `t <= 8` the following statement (EX_t) is false.

> (EX_t) Let `S_X, S_Y ⊆ K` be finite with `S_X = S_Y b`.  Then every minimal covering of `S_X ∪ S_Y` by copies
> contains a copy that meets the union of the others in at most `t` links.

**Counterexample (star family).**
- Fix at least two lines of `Gamma` and a long interval `a^{[0,R]}` of the coset `<a>`.  Take every copy whose
  chosen line lies inside that interval.
- Each copy meets the others in `<a>`.  It also meets them in the 8 cosets at the far ends of the 8 `b`-edges of
  its chosen line, because each such edge is also an edge of another copy of the family (the ends `0` and `C_l` of
  every line are both in-ports and out-ports).
- Lines at distance `>= 3` from the chosen line in `Phi` are private to their copy ([TC] Corollary 3).  So the
  covering of the port-closed supports is minimal.

**Scope.**
- The obstruction is at the level of supports.  The star family violates the coefficient input: it has many clean
  active cosets per copy, against the rank-one proposition of
  `rips-segev-three-copy-configurations-carry-no-zero-divisors`.
- Open, and the natural next statement: among port-closed patterns in which every copy has at most one clean active
  coset (each with at least three dirty port neighbours), some copy of a minimal covering has at most two dirty
  cosets.
- The construction uses only the simplicity of `Phi`, the ends of lines being ports, and the two-copy gluing
  corollaries.  It holds for every `gamma >= 42`.
