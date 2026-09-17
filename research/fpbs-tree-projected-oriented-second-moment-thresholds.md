---
rg: 2
id: fpbs-tree-projected-oriented-second-moment-thresholds
kind: claim
title: Oriented second moment and the non-backtracking resolvent give strict thresholds for tree-projected Cayley graphs of rank at least three
distinct_from:
  fpbs-tree-projected-large-rank-strict-thresholds: that uses one decoration per letter for p_c <= 1/(2n-1) and the bound 1/||A|| for p_{2->2}, so it needs n >= 19 for rigid sets; this uses all m decorations per letter through a second moment, and the non-backtracking resolvent instead of 1/||A||, and covers rank three with v <= 2 for every m >= 2.
  fpbs-tree-projected-rigid-decorations-strict-thresholds: that is the open claim for every rank and every vertical part; this settles it in rank n >= 3 under an explicit bound on the vertical part, and does not reach rank two.
  fpbs-tree-projected-sphere-bubble-l2-equivalence: that is an exact criterion through a critical estimate; this uses no critical estimate, only a Paley–Zygmund bound and a spectral radius.
artifacts:
  - experiments/tree-projected-second-moment-2026-09-17/criterion.py
  - experiments/tree-projected-second-moment-2026-09-17/output.txt
  - experiments/tree-projected-second-moment-2026-09-17/mc_rank3_rigid.py
  - experiments/tree-projected-second-moment-2026-09-17/mc-output-seed1.txt
---

**ESTABLISHED.** Let `Gamma` be finitely generated, `H` a torsion-free normal
subgroup and `pi : Gamma -> F_n = Gamma/H` with `n >= 2` and free basis `B`. Let `S`
be a finite symmetric generating set, `1 ∉ S`, with `pi(S) ⊆ {1} ∪ B ∪ B^(-1)`.
Put `b = 2n-1` and

```text
m_t = #{g in S : pi(g) = t},   m_lo = min_t m_t,   m_hi = max_t m_t   (t in B),
v   = #{g in S : pi(g) = 1},   d = |S| = v + 2 sum_t m_t,
p_o = [ b m_lo - (m_lo - 1)^2 / ((b-1) m_lo^2 + m_lo - 1) ]^(-1),
lam = v + 2 m_hi sqrt(b),
p*  = smallest positive root of (d-1) p^2 - lam p + 1   (p* = 1/sqrt(d-1) if there is none).
```

Then on `Cay(Gamma,S)`

```text
p_c <= p_o      and      p* <= p_{2->2} <= p_u.
```

Hence `p_o < p*` implies `p_c < p_u`.

**New input.**
* *`p_c` side.* A Paley–Zygmund second moment runs over open paths that follow reduced
  words of `F_n`. Such a path may use any of the `m_lo` decorations of each letter.
  Two such paths share an edge only while they follow the same word and sit at the
  same vertex. In a fibre `gH`, two distinct vertices `g, gh` lead to a common
  vertex along the same letter for at most `m_lo - 1` decoration pairs, because `H`
  is torsion-free. A `2 x 2` transfer matrix bounds the overlap sum. The case
  `m_lo = 1` returns the tree threshold `1/(2n-1)` exactly.
* *`p_u` side.* Self-avoiding paths are non-backtracking walks. The Ihara generating
  function `(1-z^2)/(1 - zA + (d-1)z^2)` is analytic for `|z| < p*` uniformly on the
  spectrum `[-lam, lam]`, which gives `p* <= p_{2->2}`. The weaker bound `1/||A||` is
  what the large-rank claim uses.

**Coverage** (exact rational check in `experiments/tree-projected-second-moment-2026-09-17/`).
The table lists the largest vertical count `v` for which `p_o < p*` holds, with
uniform multiplicity `m`. `none` means the criterion fails even at `v = 0`.

| n \ m | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 |
|---|---|---|---|---|---|---|---|---|
| 2 | 0 | 0 | none | none | none | none | none | none |
| 3 | 1 | 2 | 2 | 3 | 3 | 4 | 4 | 5 |
| 4 | 3 | 4 | 6 | 8 | 9 | 11 | 13 | 14 |
| 5 | 4 | 7 | 10 | 13 | 16 | 19 | 22 | 25 |
| 6 | 5 | 10 | 14 | 18 | 23 | 27 | 31 | 36 |

* **Rank three, rigid.** For `S = {(a,0),(a,1),(a,3),(b,0),(b,1),(b,4),(c,0),(c,1),(c,5),(1,1)}^(±1)`
  in `F_3 x Z`, the shapes `D_s` and `-D_s` are pairwise distinct up to translation.
  Here `n = 3`, `m = 3`, `v = 2` and `d = 20`, which gives
  `p_c <= 19/283 ≈ 0.06714 < 0.07109 ≈ p* <= p_u`.
  The large-rank criterion needs `n >= 21` for this vertical part. A Monte Carlo
  sanity check, which is not part of the proof, finds 6.5% of clusters reaching size
  5000 already at `p = 0.055`.
* **Corollary: uniform multiplicity, small vertical part.** If every letter carries the
  same number `m >= 2` of decorations, `v <= 2` and `n >= 3`, then `p_c < p_u`. The
  proof gives an analytic inequality for all `(n,m)` except `(3,2)`, which is checked
  exactly. The script also checks `3 <= n <= 8`, `2 <= m <= 2000` and `v in {0,2}`
  exactly. Rigid sets have `m_lo >= 3`, so
  `fpbs-tree-projected-rigid-decorations-strict-thresholds` holds in every rank
  `n >= 3` for uniform multiplicities and vertical part `{(1,±1)}` or empty. Mixed
  multiplicities need `p_o(n, m_lo) < p*(lam(m_hi), d)`, which is checked case by case.
* **Rank two is out of reach.** `p_o m -> 1/3` while `p* m -> 1/(2 sqrt 3) ≈ 0.2887`.
  The criterion fails for every `m >= 3`, including `S_rig`, where
  `p_o = 5/44 ≈ 0.1136 > 0.0890 ≈ p*`. The oriented ensemble sees only `3m` of the `4m`
  decorated tree edges at a vertex. Simulated `p_c(S_rig) ≈ 0.084` lies below `p*`,
  so a rank-two proof must count paths that return to a fibre they have already
  visited.

Proof: `fpbs-tree-projected-oriented-second-moment-proof`.
