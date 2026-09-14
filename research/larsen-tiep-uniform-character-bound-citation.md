---
rg: 2
id: larsen-tiep-uniform-character-bound-citation
kind: route
title: Larsen–Tiep, Uniform character bounds for finite classical groups, Theorem A, quoted verbatim
target: larsen-tiep-uniform-character-bound
requires: []
---

**Source.** M. Larsen and P. H. Tiep, *Uniform character bounds for finite classical groups*, arXiv:2403.09046v1 (14 March 2024), p. 2. Lane sk-characters-rigidity-b read it from the arXiv PDF on 2026-09-13.

> "Theorem A. There exists an absolute constant c > 0 such that for all finite quasisimple groups G of Lie type, irreducible characters χ of G, and elements g ∈ G, we have
> (1.1) |χ(g)| ≤ χ(1)^{1−c·log|g^G|/log|G|}."

**Definitions** (p. 1): quasisimple means `G = [G,G]` and `G/Z(G)` is a finite simple group of Lie type. The paper adds that the exponent is optimal up to a multiplicative constant, and that `c` is made explicit in the proof.

**Use in the repository.** `GL_N(F_2) = SL_N(F_2)` is simple for `N ≥ 3`, so the theorem applies to it.

**Not checked.** The journal version, and the numerical value of `c`.
