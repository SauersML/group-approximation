---
rg: 2
id: rips-segev-eight-copy-configurations-carry-no-zero-divisors
kind: claim
title: In Steenbock's Rips--Segev core no relation alpha (u(a) + w(a) b) = 0 with alpha, w != 0 has alpha u and alpha w supported on the union of eight translates of g(V(Gamma)), because a window of the shell arc sized by the shell face's own length l beats 2N + min(N, e_2) arc cosets, the girth of Phi forcing short faces to be almost all b^2
distinct_from:
  rips-segev-six-copy-configurations-carry-no-zero-divisors: that closes six translates with a fixed 12-syllable window sized by gamma and the bound 2N + e_2; this closes eight by sizing the window from the shell face's own length, counting partial end syllables, bounding the triples by min(N, e_2), and using that a face of length l has at most l - 42 single-b syllables.
  rips-segev-three-copy-configurations-carry-no-zero-divisors: that closes three translates by counting all active cosets; this is a shell-arc count, pushed to N = 8.
  rips-segev-coefficient-free-extremal-copy-lemma-fails: that shows the extremal-copy step toward every N cannot be done from supports alone; this is a fixed-N counting result.
  rips-segev-groups-satisfy-kaplansky-zero-divisor: that is the open question for all of k[G(Gamma)]; this settles the two-layer relations inside eight translates.
---

**ESTABLISHED (proposed; unreviewed).**  Derivation: `rips-segev-eight-copy-no-zero-divisors-proof`.

**Setting.**  As in `rips-segev-six-copy-configurations-carry-no-zero-divisors`.
- `Gamma` is Steenbock's graph with `Gr'_*(1/8)` and `gamma >= 42`, and its `b`-edges project to an 8-regular
  graph `Phi` of girth `>= 42`.
- `K` is the core, and `G = G_1 *_{<a>} K *_{<b>} G_2`.
- A *copy* is `h g(Gamma)`, with vertex set `V_h = h g(V(Gamma))`.

**Theorem.**  Let `k` be a field, `u, w in k[<a>]`, and `alpha in k[K]`, with `alpha != 0`, `w != 0` and
`alpha (u + w b) = 0`.  Then there are no `h_1, ..., h_8 in K` with
`supp(alpha u) ∪ supp(alpha w) ⊆ V_{h_1} ∪ ... ∪ V_{h_8}`.  The same holds in `k[G]`, with `h_m in G`.

**How.**
- *Face shape.*  The shell face `M` of the port cycle's diagram has syllable length `l >= 42`, and it has
  `l/2` `b`-syllables.  Its `b`-edges project to a closed non-backtracking walk in `Phi`, so at most `l - 42` of
  them are single `b`'s.  At `l = 42` all of them are `b^2`.
- *Window.*  Greendlinger gives an exterior arc of more than `5l/8` syllables.  A window in it with `n*`
  `b`-syllables, `e*` of them whole `b^2`, and `n* + e* <= 39` edges visits `n* + e* + 1` distinct active cosets.
- *Criterion.*  `N` copies other than the shell copy see at most `2N + min(N, e*)` of these cosets.  With the
  rank-one purity argument for the shell inside the covering, a counterexample is impossible as soon as
  `n* + max(0, e* - N) >= 2N`.
- At `N = 8` this holds for every `l`.
  - `l = 42`: 27 syllables, `13 + 5` or `14 + 4`.
  - `l = 44, 46, 48`: `14 + 3`, `14 + 2` or `15 + 1`, and `15 + 1` or `16`.
  - `l >= 50`: `n* = 16`.

**Also proved.**
- *Exact `N = 9` residue.*  The shell face has length `42 <= l <= 54`, and the diagram has at least three faces.
  Longer faces, and diagrams with at most two faces, close.
- The window criterion cannot pass about `N = 12`, whatever the face length, because it needs `n* + e* <= 39`.

**Scope.**  Every `N` is the whole `b`-degree-one case of `rips-segev-groups-satisfy-kaplansky-zero-divisor`,
and it stays open.  An induction on `N` needs the extremal-copy step.  Its coefficient-free form is false
(`rips-segev-coefficient-free-extremal-copy-lemma-fails`), and its coefficient-aware form is not proved here.
