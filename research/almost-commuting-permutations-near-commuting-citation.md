---
rg: 2
id: almost-commuting-permutations-near-commuting-citation
kind: route
title: Import the Main Theorem of Arzhantseva--Paunescu, Almost commuting permutations are near commuting permutations
target: almost-commuting-permutations-are-near-commuting
requires: []
---

**Established by citation.** Goulnara Arzhantseva and Liviu Păunescu, *Almost commuting permutations
are near commuting permutations*, J. Funct. Anal. 269 (2015), 745--757, arXiv:1410.2626v2. Read from the
arXiv PDF, 2026-09-12.

- **Main Theorem**, p. 2, verbatim: "For any given k >= 2 and with respect to the normalized Hamming
  distance, every k (even) permutations that almost commute are near k commuting (respectively, even)
  permutations."
- The precise meaning is their **Definition 3.2**, p. 5. Permutations `p_1, ..., p_m` are a
  `delta`-solution of a finite word set `R` if `d_H(xi(p_1, ..., p_m), id_n) < delta` for all `xi in R`.
  "The system R is called stable (or stable in permutations) if for all epsilon > 0 there exists
  delta > 0 for all n in N* for all p_1, ..., p_m in Sym(n) a delta-solution of R, there exist
  p~_1, ..., p~_m in Sym(n) a solution of R such that d_H(p_i, p~_i) < epsilon."
- The Main Theorem is stability of `R = {[x_i, x_j]}`. The same paper's Open problem (p. 3) asks the
  same question for the two relators of Thompson's `F`; see
  `thompson-f-relator-system-stable-in-permutations`.
