---
rg: 2
id: integral-matrices-of-norm-below-3-over-sqrt2-obey-serre
kind: claim
title: Over every group a self-adjoint integral matrix of signed norm below 3/sqrt2 obeys every Serre inequality
distinct_from:
  integral-matrices-of-norm-below-2-019-obey-serre: that is the proved range up to 2.019 via the McKee--Smyth table; this asks for the signed range up to 3/sqrt2 = 2.1213, where no finite table exists
  tripod-free-integral-matrices-reduce-to-virtually-cyclic: that proves Serre when the absolute norm ||r_|A||| is below 3/sqrt2; this asks the same for the signed norm ||r_A||, which can be much smaller than the absolute norm through cancellation
  determinant-conjecture-counterexample-exists: that asks for a violation anywhere; this would force any violating matrix, and all its integral polynomial images, to have signed norm at least 3/sqrt2
artifacts:
  - research/artifacts/determinant-norm-room-2026-09-16.md
---

**OPEN.** Let `G` be any group and `A in M_n(Z[G])` self-adjoint with
`||r_A|| < 3/sqrt 2`. Then `integral_{Q!=0} log|Q| d mu_A >= 0` for every
nonzero `Q in Z[x]`.

**Why this threshold.** `3/sqrt 2` is the supremum of the spectral radii of
the tripods `T_(k,k,k)`.
- Below it, nonnegative matrices have finite or virtually cyclic component
  stabilizers (`tripod-free-integral-matrices-reduce-to-virtually-cyclic`).
- For every `eps > 0`, nonnegative matrices of norm below `3/sqrt 2 + eps`
  exist over every finitely generated group with that group as stabilizer. They
  carry every Serre violation of cubic operators of norm below `3`
  (`cubic-serre-violations-transfer-to-norm-near-3-over-sqrt2`).

So for nonnegative matrices this bound is exactly where the room for a
violation opens. The claim asks whether signs can open it earlier.

A violation below `3/sqrt 2` needs two things:
- a graph component whose stabilizer is nonsofic, since sofic stabilizers give
  Serre by the decomposition of the artifact, Corollary 1.2;
- no long induced uncharged tripods (artifact, Lemma 6.1(4)).

## Attempts

- **McKee--Smyth past 2.019.** Dead as a finite table. Finite noncyclotomic
  graphs `T_(1,2,m)` of unbounded size have radius below `2.0198...`, and
  above that there are infinitely many. The signed range
  `(2, sqrt(2 + sqrt 5))` is not classified (McKee--Smyth, arXiv:0907.0371,
  Section 1). The argument of `integral-matrices-of-norm-below-2-019-obey-serre`
  needs a size bound on noncyclotomic components, and this bound fails.
- **Absolute tripods.** Theorem A of the artifact excludes tripod subgraphs
  only through `||r_|A|||`. In signed graphs, a tree subgraph with chords does
  not bound the signed norm. Only induced, uncharged trees do, after switching
  signs.
- **Local structure (proved, artifact Lemma 6.1).** If `||r_A|| < 3/sqrt 2`:
  - every row of `r_A` has squared norm at most `4`, so the degree is at most
    `4` and entries are `+-1` except isolated `+-2`;
  - a 4-valent vertex `v` has `r_A^2 delta_v = 4 delta_v + eps delta_w` with
    `eps in {0, +-1}`;
  - pure vertices (`eps = 0`) carry spectral measure on `{+-2}`.

  This leaves open whether growth can be exponential. The local test is not
  sufficient. The signed Cayley graph of `Z/4 * Z/2`, with every square
  negative, passes it at every vertex, yet a 17-vertex ball already has radius
  `2.23607 > 3/sqrt 2`. Larger balls approach `1 + sqrt 2`
  (`experiments/determinant-norm-room-2026-09-16/signed_square_tree.py`). The
  remaining test family is signed 4-regular strips ("tubes") joined at
  junctions of degree at most `3`. No norm computation for such trees of tubes
  was done.
- **Growth or amenability.** A positive answer would follow if every component
  of `Gamma_A` with `||r_A|| < 3/sqrt 2` had a sofic stabilizer, for instance an
  amenable one. Linear growth is proved at signed norm at most `2`
  (`norm-two-integral-matrices-reduce-to-virtually-cyclic-groups`). It fails for
  absolute norm just above `3/sqrt 2`. For signed norm in `(2.019, 3/sqrt 2)`,
  neither linear nor subexponential growth is known, and no example of
  exponential growth is known either.
