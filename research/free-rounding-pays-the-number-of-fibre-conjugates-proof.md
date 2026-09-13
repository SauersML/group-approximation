---
rg: 2
id: free-rounding-pays-the-number-of-fibre-conjugates-proof
kind: route
title: Run the primitive-kernel halving chain successively on all conjugates of K; the wreath-product family gives the matching lower bound
target: free-rounding-pays-the-number-of-fibre-conjugates
requires: [primitive-projective-representations-have-a-trace-gap, galois-games-round-through-free-subgroups, galois-unique-game-value-is-transversal-expansion, free-subgroup-rounding-fails-for-non-normal-fibres]
artifacts:
  - research/artifacts/ugc-rounding-normal-fibres-2026-09-13.md
  - research/artifacts/ugc-rounding-normal-fibres-part2-2026-09-13.md
---

Complete proofs: Theorem 14 of part 3 and Corollary 17 of part 4.

* **Good kernels avoid every conjugate.** Step (ii) of irreducible-kernel
  rounding in `galois-games-round-through-free-subgroups` gives
  `K cap (intersection of good ker rho) = {e}`. Each `ker rho` is normal, so the
  same holds for every conjugate `K_j = y K y^-1`.
* **Mass of one primitive kernel.** As in
  `normal-fibre-galois-games-round-linearly-over-all-groups-proof`, with the
  required trace gap: `mu(G \ x (ker sigma) x^-1) <= 3 eps/c(G,m)`.
* **Chain over all conjugates.** Keep a running intersection `L`. While some
  `K_j cap L` contains `a != e`, choose a good `rho` with `a notin ker rho` and a
  conjugate of its primitive kernel omitting `a`, and intersect. Each step divides
  one `|K_j cap L|` by at least `q`, so there are at most `r log_q k` steps. At the
  end `L` meets every conjugate trivially, so it is free on `G/K` (part 1 of the
  required claim).
* **Lower bound.** The required counterexample has `r = N` and `k = 2`, and every
  free `H` loses `>= (N-1) eps`.
