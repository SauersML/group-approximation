---
rg: 2
id: sl2-z-inverse-p-is-flexibly-hs-stable
kind: claim
title: SL2(Z[1/p]) is flexibly Hilbert--Schmidt stable for some prime p
distinct_from:
  iwahori-local-global-defect-question: that is Dogon--Vigdorovich Question 1.4, the local-to-global Iwahori modulus for SL_2(Z) *_(Γ_0(2)) SL_2(Z); by sl2-half-stability-excludes-hnn-hyperlinearity a positive answer is flexible stability of SL_2(Z[1/2]). This is the same stability statement for an arbitrary prime p, recorded as its own node because sl2-pq-flexibility-from-sl2-p-flexibility consumes it for every p != q.
  sl2-z-inverse-pq-is-flexibly-hs-stable: that is the two-prime lattice; by sl2-pq-flexibility-from-sl2-p-flexibility this one-prime statement implies it.
  hnn-over-sl2-z-not-sofic-if-sl2-z-inverse-p-p-stable: that is permutation stability of SL_2(Z[1/p]) and a non-sofic conclusion; this is flexible Hilbert--Schmidt stability.
---

**OPEN.** There is a prime `p` for which `SL_2(Z[1/p])` is flexibly
HS-stable in the sense of Dogon--Vigdorovich, Definition 1.2 of
arXiv:2506.20843. The notion is the one used in
`sl2-z-inverse-pq-is-flexibly-hs-stable`.
- Take any sequence of unitary tuples on a fixed finite generating set whose
  relator defect tends to `0`.
- Then there are exact representations of dimensions `D_n >= d_n`, with
  `D_n/d_n → 1`.
- Their compressions to `d_n`-dimensional subspaces are `o(1)`-close to the
  tuples in normalized Hilbert--Schmidt norm.

**Consequences.**
- For `p = 2` this is the positive answer to Dogon--Vigdorovich Question 1.4
  (`iwahori-local-global-defect-question`, `sl2-half-stability-excludes-hnn-hyperlinearity`).
- For every `p`, the `(tau)` form of `hnn-over-codense-kazhdan-subgroup-not-hyperlinear`,
  with `sl2-z-inverse-p-over-sl2-z-is-codense-tau-pair`, makes
  `<SL_2(Z[1/p]), t | [t, SL_2(Z)] = 1>` non-hyperlinear.
- By `sl2-pq-flexibility-from-sl2-p-flexibility`, it gives
  `sl2-z-inverse-pq-is-flexibly-hs-stable` for this `p` and every prime `q != p`.

**What would refute it.** For each `p` separately, a sequence of asymptotic
representations of `SL_2(Z[1/p])` far from all congruence representations.
By `sl2-pq-exact-vertex-pairs-have-uniform-linear-repair`, such a sequence is
also the only way to refute `sl2-z-inverse-pq-is-flexibly-hs-stable` through
its q-adic amalgam decomposition. A pair of exact vertex representations can
never witness a refutation.
