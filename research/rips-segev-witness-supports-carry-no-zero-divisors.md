---
rg: 2
id: rips-segev-witness-supports-carry-no-zero-divisors
kind: claim
title: In Steenbock's small-cancellation Rips--Segev groups no zero-divisor pair lives inside the non-unique-product witness (A, B), over any field and for any supports
distinct_from:
  rips-segev-witness-pairs-carry-no-zero-divisors: that kills only the exact supports supp alpha = A, supp beta = {1,a,b,ab} and assumes the exact encoding (EE); this proves (EE) from graphical small cancellation and kills every pair with supp alpha inside A and supp beta inside B.
  rips-segev-groups-satisfy-kaplansky-zero-divisor: that is the conjecture for the whole group ring; this rules out the one support region that the non-unique-product construction singles out.
  cyclic-centralizer-groups-have-no-support-three-zero-divisors: that asks about every support-three element in a large host class; this covers beta of support three or four inside B only, with no bound on alpha inside A.
artifacts:
  - experiments/rips-segev-coefficient-rigidity-2026-09-17/spaced_gap_check.py
  - experiments/rips-segev-coefficient-rigidity-2026-09-17/spaced_results.txt
---

**ESTABLISHED (proposed; unreviewed).**  Derivation: `rips-segev-witness-supports-carry-no-zero-divisors-proof`.

**Setting.**  Steenbock, arXiv:1307.0981, Section "Generalized Rips-Segev groups".
- `G_1, G_2` are finitely generated torsion-free groups, `1 != a in G_1`, `1 != b in G_2`, `F = G_1 * G_2`.
- `Gamma` is a generalized Rips--Segev graph with coefficients `(I,O,C)` and `K` lines, with each `c_i` the label
  of a shortest path from `v_10` to `v_i0`, so that `Gamma = Theta'` (Steenbock's remark opening "Graphical small
  cancellation").
- `A = sqcup_i {c_i a^l : 0 <= l < C_i}` and `B = {1, a, b, ab}`.
- The *distinguished positions* of line `i` are `0`, `C_i`, the Step 1 targets `I_ij` and the Step 2 targets
  `O_ik`.

**Theorem.**  Suppose the labeling of `Gamma` satisfies `Gr'_*(1/8)` over `F`, and at most one pair of
distinguished positions on a common line lies at distance one.  Let `k` be any field.  If `alpha, beta in
k[G(Gamma)]` are nonzero with `supp alpha` inside `A` and `supp beta` inside `B`, then `alpha beta != 0`.

**Coverage.**  The hypotheses hold for Steenbock's explicit families: coefficients satisfying the Rips--Segev
condition over an underlying graph of girth at least 41 (Steenbock's corollary on the final graphical small
cancellation condition and the Explicit constructions subsection).
- The Rips--Segev condition makes all distances between distinguished positions nonzero and pairwise distinct.
  So at most one of them equals one.
- The coefficient table `(10^{5i-4}, ..., 10^{5i})` has no distance equal to one at all.

**Proof outline.**
1. **Exact encoding (EE) holds.**
   - Vertices of `Gamma` inject into the Cayley graph (Steenbock, Theorem "gi").
   - A product `v_il b` whose `b`-edge was deleted in Step 3 is never a vertex of `Gamma` in `G(Gamma)`.  This is
     a van Kampen argument that mirrors the proof of Theorem "gi": the outer arc of an exterior face is made of at
     most two pieces and one `b`-letter, which is too short for the graphical small cancellation lemma.
   - Two such hanging products coincide only if their base vertices do.
2. **Gap argument.**  Write `beta = p + x a + y b + z ab`.  At an index `l` with `1 <= l <= C_i - 1` that is not
   distinguished, (EE) says the coefficients of `v_il` and `v_il b` in `alpha beta` are
   `p alpha(l) + x alpha(l-1)` and `y alpha(l) + z alpha(l-1)`.
   - If `pz != xy`, both vanishing forces `alpha(l) = alpha(l-1) = 0`.
   - The distinguished positions `0 = d_0 < d_1 < ... < d_r = C_i` cut `[0, C_i - 1]` into the blocks
     `[d_s, d_{s+1} - 1]`.  Each block with `d_{s+1} - d_s >= 2` contains such an `l = d_s + 1` and is killed by
     the recurrence.  So `alpha` survives only at an index `d` with `d, d+1` both distinguished.
   - There is at most one such index, so `alpha` is a monomial, and a monomial is never a zero divisor.
3. **Rank one.**  If `pz = xy`, then `beta = (u + v a)(s + t b)` with both factors nonzero.  Such factors are
   non-zero-divisors in any torsion-free group (Lemma 0 of `rips-segev-witness-pairs-carry-no-zero-divisors-proof`).
   `G(Gamma)` is torsion-free (Steenbock, Theorem "tf"), and `a, b != 1` there because `B` embeds.

**What this kills.**  The attempt is "a zero divisor of a Rips--Segev group sits on the configuration that
destroys unique products".
- It dies at step 2 for every coefficient pattern of rank two: the free a-line indices between consecutive
  distinguished positions form clean squares.
- It dies at step 3 for rank one.
- A counterexample in `k[G(Gamma)]` needs `supp alpha` to leave `A` or `supp beta` to leave `{1,a,b,ab}`.  The
  small-cancellation encoding gives no control there.

**Computation** (`spaced_gap_check.py`; commands and outputs in `spaced_results.txt`).  This checks step 2 in the
exact pattern model for random Steps 1--2 gluings with `K <= 3` lines, over every nonzero `beta` in `F_q^4`,
computing the whole kernel of `alpha -> alpha beta`.
- With no adjacent distinguished pair (300 graphs over `F_2` and over `F_3`): rank-two `beta` never has a nonzero
  kernel.
- With at most one adjacent pair (300 graphs over `F_3`, 100 over `F_5`): every rank-two kernel vector is a
  monomial.
- *Calibration.*  With unrestricted gluings, 308 rank-two rows over `F_3` have kernel vectors of support at least
  two.  The spacing hypothesis is therefore used.  Rank-one `beta` do have pattern kernels in many random gluings;
  those gluings are not small cancellation, as the pattern remark in `rips-segev-witness-pairs-carry-no-zero-divisors`
  explains.
