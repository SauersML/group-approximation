---
rg: 2
id: length15-16-free-piece-residue-via-linton-certificates
kind: route
title: Run the graph-of-cyclic-stabilisers certificate on the length-15 and length-16 residue lists
target: length15-16-free-piece-residue-classes-hyperbolic-special
requires:
  - linton-graph-certificate-for-free-magnus-pieces
artifacts:
  - research/artifacts/one-relator-linton-graph-certificates-scripts/lintongraph.py
  - research/artifacts/one-relator-linton-graph-certificates-scripts/lg.sbatch
  - research/artifacts/one-relator-linton-graph-certificates-scripts/lg.720594.log
  - research/artifacts/one-relator-linton-graph-certificates-scripts/lg_l15.out
  - research/artifacts/one-relator-linton-graph-certificates-scripts/lg_seq16.out
  - research/artifacts/one-relator-linton-graph-certificates-scripts/lg_words16.out
  - research/artifacts/one-relator-linton-graph-certificates-scripts/census3_16.out
---

**Inputs.**
- Length 15: the 30 `REST` classes of `residue-output.txt` (landed with the length-15 residue).
- Length 16: the 211 `REST` lines of `census3.py 16 16 100000`, regenerated on MSI (job 717895,
  `census3_16.out`). Its counts match the census table in
  `research/artifacts/or-unpeelable-extreme-2026-09-12.md`: 230 survivors, 211 after the
  partial-positivity search.

**Normal form.** For a relator with exponent sums `(p, q) != (0, 0)`, `lintongraph.py words` applies
the Nielsen automorphism `census.adapt(w, q/g, -p/g)` (with `g = gcd(p, q)`), which presents the same
group with `t`-exponent sum 0, and takes the Magnus rewriting `census.magnus` in the canonical form
`census.canon`. Rotation, reversal, inversion and reflection of levels preserve the group. The
Magnus piece is recognised as free when an interior level letter occurs exactly once
(`malnormal.free_piece`), and only level gcd 1 is used.

**Run.** MSI job 720594 (`lg.sbatch`, `lintongraph.py` md5 `61fb8fe94a71be996a307db09f7e037a`):
- `words residue-output.txt`: 30 `VERDICT` lines, all `-> PASS`, every one with `rank=2`,
  `sZ=(2, 2)`, `hloops=0`, `tloops=0`, `cycle=False`.
- `words census3_16.out`: 211 classes. 70 end `-> PASS` (44 with an exponent sum zero, 26 with both
  nonzero), all with `rank=2`, `sZ=(2, 2)`, no loops and no alternating cycle. 141 are `NONFREE`.
- `census 16` (the exponent-sum-zero Magnus census, 176 classes before the partial-positivity search)
  independently gives 48 `PASS` (the 44 above plus 4 partially positive ones) and 128 `NONFREE`,
  matching `malnormal.py 16` (job 717895).

Each `PASS` line records (C0)–(C3) of `linton-graph-certificate-for-free-magnus-pieces`: rank 2 edge
groups, the enumeration depth, `sZ`, the vertex list, edge counts, loop counts and the cycle test. So
every listed group is hyperbolic, has no Baumslag–Solitar subgroup, and is virtually special.

**Trust surface.** The census code (`census.py`, `census2.py`, `census3.py`, `malnormal.py`) as
landed on 2026-09-12, and `lintongraph.py`. The generator was calibrated on row 29, on Linton's
Examples 1.2 and 6.12 and on the length-15 list (artifact §3); no independent reimplementation was
run.

_Orphan sweep (2026-09-14): this node cited `research/artifacts/one-relator-linton-graph-certificates-2026-09-13.md`, which its lane never wrote to the repository and which could not be recovered from the lane transcript._
