---
rg: 2
id: rips-segev-six-copy-configurations-carry-no-zero-divisors
kind: claim
title: In Steenbock's Rips--Segev core no relation alpha (u(a) + w(a) b) = 0 with alpha, w != 0 has alpha u and alpha w supported on the union of six translates of g(V(Gamma)), because a shell arc of the port cycle touches 13 + e_2 distinct active cosets while each covering copy other than the shell copy meets at most two of them, or three forming one of the e_2 b^2-syllables
distinct_from:
  rips-segev-three-copy-configurations-carry-no-zero-divisors: that closes three translates by counting all active cosets (N + 3N(N-1)/2) and leaves N = 4 at an unresolved residue; this closes N <= 6 with the same coefficient input, by charging every coset of a shell arc and showing that a single other copy sees at most two of them unless it shares a whole b^2-syllable with the shell.
  rips-segev-two-copy-configurations-carry-no-zero-divisors: that handles two translates; this uses its gluing corollaries (a bridge is the only link; at most three shared cosets, pairwise joined by shared b-runs) as the only geometric input about pairs of copies.
  rips-segev-coefficient-free-extremal-copy-lemma-fails: that shows the extremal-copy step toward every N cannot be done from supports alone; this is the fixed-N counting result, pushed to N = 6.
  rips-segev-groups-satisfy-kaplansky-zero-divisor: that is the open question for all of k[G(Gamma)]; this settles the two-layer relations inside six translates.
---

**ESTABLISHED (proposed; unreviewed).**  Derivation: `rips-segev-six-copy-no-zero-divisors-proof`.

**Setting.**  As in `rips-segev-three-copy-configurations-carry-no-zero-divisors`: `Gamma` is Steenbock's graph
with `Gr'_*(1/8)` and `gamma >= 42`, `K` is its core, `G = G_1 *_{<a>} K *_{<b>} G_2`, and a *copy* is `h g(Gamma)`
with vertex set `V_h = h g(V(Gamma))`.

**Theorem.**  Let `k` be a field, `u, w in k[<a>]`, and `alpha in k[K]`, with `alpha != 0`, `w != 0` and
`alpha (u + w b) = 0`.  Then there are no `h_1, ..., h_6 in K` with
`supp(alpha u) ∪ supp(alpha w) ⊆ V_{h_1} ∪ ... ∪ V_{h_6}`.  The same holds in `k[G]`, with `h_m in G`.

**How.**
- Take a port cycle (a positive relation of `K` read along the supports) and a Greendlinger shell face of its
  minimal diagram, in a copy `C_M`.  Its exterior arc contains 12 consecutive `b`-syllables, `e_2` of them equal to
  `b^2`.  The arc visits `13 + e_2` cosets, pairwise distinct (girth of `Phi`), and all active.
- *Two-or-a-syllable lemma.*  A copy other than `C_M` meets at most three of these cosets.  If it meets three,
  they are consecutive and form one `b^2`-syllable.  The reason: the three are pairwise joined by shared `b`-runs,
  and a run and the arc walk can only differ by closing a cycle of length `<= 26` in `Phi`.  So `n` copies other
  than `C_M` meet at most `2n + e_2` of the arc cosets.
- *Shell outside the covering.*  Every arc coset meets a covering copy, so `13 + e_2 <= 2N + e_2`.
- *Shell inside the covering.*  At most one arc coset is pure (rank-one lemma), and every impure one is linked to
  another covering copy, so `12 + e_2 <= 2(N - 1) + e_2`.
- `N = 6` fails both.

**Also proved.**
- For girth `g` the `N`-copy theorem holds whenever `2N <= B ≈ 5g/16`.  The previous bound was about `5g/48`.
- *Three-port lemma.*  In a counterexample every clean active coset has at least three port edges.  They end on
  distinct lines adjacent to it, all dirty.  The reason: one in-port and one out-port would make `u` and `w`
  monomials, and `c + e a^r b` is a non-zero-divisor.
- Exact residue at `N = 7`: the shell copy is in the covering, exactly one arc coset is pure, and the other six
  copies see disjoint sets of arc cosets, `e_2` of them a whole `b^2`-syllable each and the rest exactly two each.

**Scope.**  Every `N` is the whole `b`-degree-one case of `rips-segev-groups-satisfy-kaplansky-zero-divisor`.
It stays open.  The fixed-length shell arc limits any count of this kind to `N = O(g)`.  The coefficient-free
extremal-copy lemma that would drive an induction is false
(`rips-segev-coefficient-free-extremal-copy-lemma-fails`).
