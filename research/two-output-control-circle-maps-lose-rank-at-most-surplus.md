---
rg: 2
id: two-output-control-circle-maps-lose-rank-at-most-surplus
kind: claim
title: A continuous map between finite products of circles in which each input is coarsely determined by at most two outputs loses first-cohomology rank at most its surplus of outputs, with no locality hypothesis
distinct_from:
  local-rectangular-small-fibre-maps-lose-proportional-rank: that is LRSF for all K and d, assuming both locality and control (OPEN); this proves its linear form at d = 1 and control sets of size at most 2, with the sharp constant C = 1 and without the locality hypothesis.
  lef-groups-are-torus-surjunctive: that contains the square, dimension-free small-fibre lemma, proved through top homology of T^N; this is a rectangular statement with surplus, proved through cup products of coarse-inverse classes and a level-strip argument, and reduces to the square case only when the surplus is zero.
  sofic-torus-c2-reduces-to-rectangular-small-fibres: that reduces sofic C2 to LRSF; this proves one case of LRSF and leaves the reduction unchanged.
artifacts:
  - research/artifacts/two-output-control-rank-2026-09-19.md
---

Let `I, J` be finite, `eta > 0`, and `g: T^I -> T^J` continuous. Suppose each input `i`
has a set `C_i ⊆ J` with `|C_i| <= 2` such that `eta`-closeness of `g(u), g(u')` on
`C_i` forces `||u_i - u'_i|| < 1/16`. Then

    rank (g^*: H^1(T^J; Z) -> H^1(T^I; Z)) >= 2|I| - |J| = |I| - (|J| - |I|).

**What this changes.**
- The linear form of LRSF holds at `K = 2`, `d = 1`, with `C = 1`. The constant is
  sharp: Proposition S at `k = 1` attains equality.
- Locality (L) is not used. The node's remark that locality is necessary rests on an
  example whose control sets have size `N`, so for bounded control sets the need for
  (L) is open when `K >= 3`, and it is not needed when `K = 2`.
- The bound fails for control sets of size 3: tori of revolution have rank `0 < |I| - (|J| - |I|)`.
- For general `K`, the same method proves Lemma D_K: an input outside the row span of
  its control rows forces a rank drop of at least 2 among those rows. It also reduces
  the `d = 1` linear form to a counting inequality (E_K) on those inputs.
  (E_K) holds with `c_2 = 1/2` and is open for `K >= 3` (artifact, Section 7).

**ESTABLISHED 2026-09-19** by
[[two-output-control-circle-maps-lose-rank-at-most-surplus-proof]]. Agent-verified only.
