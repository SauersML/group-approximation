---
rg: 2
id: lcs-perfect-hardness-from-weighted-conjugacy-source
kind: route
title: Lower a uniformly gapped involutory-word source through bounded conjugacy bundles and tracial rounding
target: lcs-perfect-quantum-completeness-re-hardness
requires:
  - lcs-weighted-conjugacy-halting-gap-source
  - lcs-construct-weighted-conjugacy-to-lcs
artifacts:
  - research/artifacts/lcs-constructive-compiler-2026-09-20.md
---

Use the proved compiler on each source requirement. Its explicit block
formulas preserve e_*=0 as quantum value one, with no attainment premise.
To meet the exact succinct interface, Section 8 of the artifact samples
the conjugacy bundle with five fair bits, giving each of its 22 rows
probability at least 1/32. The intermediate game, with uniform variable
selection, has energy constant C'_k=max(9k^2,21312), independent of
source sizes and distributions. Culf's Corollary 7.3 and the proved
decoder give quantum gap gamma_0=(Delta/(148 C'_k))^4/K for K=max(k,3).

To make variable selection exactly samplable too, put
P=2^ceil(log2 K). Pad each row to its next power-of-two width using
private identity variables. After selecting an intermediate row, the
final verifier uses probability 1/2 for its padded row and probability
1/2 for a singleton identity check selected with log2 P fair bits.
Unused singleton slots check one distinguished identity variable.
Every final row has power-of-two width at most P, and Bob is uniform
within that row, preserving the strict LCS convention.

Section 8 proves directly for unrestricted quantum strategies that
discarding dummy answers and repairing the original parity extracts an
intermediate-game strategy with loss at most 2P^2 times the final loss.
Extending all dummy variables by +1 preserves value-one completeness.
The nonhalting quantum value is therefore at most 1-gamma, where
gamma=gamma_0/(2P^2)=(Delta/(148 C'_k))^4/(2K P^2)>0.
Choose a fixed rational
0<eta<min(gamma,1); then s=1-eta is an admissible constant soundness.
The source sampler and row decoder, with constant extra random bits,
give polynomial-time target sampling and verification, polynomial-length
questions, and at most P answer bits. Thus all requirements of the
strong root hold. No construction of the missing source is asserted.
