---
rg: 2
id: rips-segev-nine-copy-configurations-carry-no-zero-divisors
kind: claim
title: In Steenbock's Rips--Segev core no relation alpha (u(a) + w(a) b) = 0 with alpha, w != 0 has alpha u and alpha w supported on the union of nine translates of g(V(Gamma)), because Gauss--Bonnet on the port-cycle diagram gives either a shell with at most two interior arcs, whose arc window closes, or six shells with three, whose arcs carry more b-edges than the 117 active cosets allow
distinct_from:
  rips-segev-eight-copy-configurations-carry-no-zero-divisors: that closes eight translates from one shell face given by Greendlinger's lemma; this closes nine by counting curvature over all shell faces, and closes the exact residue left there (face length 42..54, at least three faces) by adding the b-edges of six shell arcs against the bound on active cosets.
  rips-segev-three-copy-configurations-carry-no-zero-divisors: that closes three translates by comparing the length of the whole port cycle with the active-coset bound; this uses the same bound, but against the b-edges on six disjoint shell arcs.
  rips-segev-coefficient-free-extremal-copy-lemma-fails: that shows the extremal-copy step toward every N cannot be done from supports alone; this is a fixed-N counting result.
  rips-segev-groups-satisfy-kaplansky-zero-divisor: that is the open question for all of k[G(Gamma)]; this settles the two-layer relations inside nine translates.
---

**ESTABLISHED (proposed; unreviewed).**  Derivation: `rips-segev-nine-copy-no-zero-divisors-proof`.

**Setting.**  As in `rips-segev-eight-copy-configurations-carry-no-zero-divisors`.
- `Gamma` is Steenbock's graph with `Gr'_*(1/8)` and `gamma >= 42`.  Its `b`-edges project to an 8-regular
  graph `Phi` of girth `>= 42`.
- `K` is the core, and `G = G_1 *_{<a>} K *_{<b>} G_2`.
- A *copy* is `h g(Gamma)`, with vertex set `V_h = h g(V(Gamma))`.

**Theorem.**  Let `k` be a field, `u, w in k[<a>]` and `alpha in k[K]`, with `alpha != 0`, `w != 0` and
`alpha (u + w b) = 0`.  Then there are no `h_1, ..., h_9 in K` with
`supp(alpha u) ∪ supp(alpha w) ⊆ V_{h_1} ∪ ... ∪ V_{h_9}`.  The same holds in `k[G]`, with `h_m in G`.

**How.**
- *Curvature.*  The minimal diagram `D` of the port cycle is a disc, because the cycle's path is simple.
  - Give each corner at an interior vertex of degree `d` the angle `2 pi / d`, and each corner at a boundary vertex
    of degree `d` the angle `pi / (d - 1)`.  Then the face curvatures sum to `2 pi`.
  - Under `C'(1/8)`, interior faces and faces with at least two exterior arcs have curvature `<= 0`.
  - A *shell*, a face with one exterior arc and `i` interior arcs, has curvature `<= (4 - i) pi / 3`.
  - So the shells satisfy `sum (4 - i) >= 6`.
- *Short shells.*  A shell with `i <= 2` has an exterior arc of more than `3l/4` syllables.  A window in it
  meets the eight-copy window criterion at `N = 9`, `n* + max(0, e* - 9) >= 18`, for every face length `l`.
- *Long shells.*  A shell with `i = 3` and `l >= 56` also has such a window.
- *Counting.*  Otherwise at least six shells have `i = 3` and `42 <= l <= 54`.
  - The girth of `Phi` forces their faces to be mostly `b^2`, so each exterior arc carries at least
    `beta(l) >= 21` `b`-edges (`beta = 26, 25, 24, 24, 23, 22, 21` for `l = 42, ..., 54`).
  - The arcs are disjoint on the boundary, which has exactly `L` `b`-edges.  So `L >= 126`.
  - But `L` is at most the number of active cosets, and that is `<= N + 3N(N-1)/2 = 117`.  Contradiction.

**Scope.**
- This closes the exact `N = 9` residue left open by the eight-copy theorem.
- It does not reach `N = 10`.  There the shells with `i = 3` survive up to `l = 62`, and six of them carry far
  fewer `b`-edges than `A(10) = 145`.
- Every `N` is the whole `b`-degree-one case of `rips-segev-groups-satisfy-kaplansky-zero-divisor`, and it stays
  open.
- An induction on `N` needs the extremal-copy step.  Its coefficient-free form is false
  (`rips-segev-coefficient-free-extremal-copy-lemma-fails`), and its coefficient-aware form is not proved here.
