---
rg: 2
id: fpbs-morse-mass-bounded-by-relator-boundary-rank-proof
kind: route
title: The matched-edge projection of the relator boundary has dense range by induction on recovery-tree height
target: fpbs-morse-mass-bounded-by-relator-boundary-rank
requires:
  - fpbs-bernoulli-morse-collapse-criterion
  - fpbs-graphing-cost-betti-cycle-dimension-identity
artifacts:
  - research/artifacts/fpbs/docs/morse-l2-inequality-and-lamplighter-gap.md
---

Written derivation, Sections 1–3 of the artifact.

1. **Modules.** Use the Hilbert-module conventions imported by `fpbs-graphing-cost-betti-cycle-dimension-identity`
   (Section 2 of `cost-cycle-structure.md`): an edge set `E` gives a module of dimension `nu(E)`, dimension is
   additive, monotone and continuous, and a closed image has dimension at most its domain. The boundary `d2^R` is a
   finite-formula module map.
2. **Removed-edge mass.** `nu(E_M) = mu(M)`, from the proof of Theorem A(b) of `fpbs-bernoulli-morse-collapse-criterion`.
3. **Dense range.** If `eta` is supported on `E_M` and `(d2^R)^* eta = 0`, then at `e = M(c)` (M1) gives
   `eta(e) = -+ (signed sum of eta over the other traversals of bd(c))`. Those edges are unmatched or children of lower
   recovery-tree height, and the heights are finite a.e. by (M3) and König's lemma (proof of Theorem A(a)). Induction
   on height, using that the child maps are Borel partial translations and so preserve null sets, gives `eta = 0`.
4. **Count.** `mu(M) = dim C_1(E_M) = dim cl P(Z_R) <= dim Z_R`.
5. **Decomposition.** `Z_R ⊆ Z` gives `gap >= 0`. A closed path of length at most `L` reads a word of `P_L`, so
   `Z_(P_L)` is the span of cycles of length at most `L`, and `gap(P_L) = z - z_L -> 0` by continuity of dimension
   (the fixed-graphing statement of the identity). Theorem B(ii) of the collapse criterion then gives
   `C_sub(S) - 1 - beta_1 = lim_L A(P_L)`.
6. **Calibrations.** The `m` cells of a proper power share one boundary chain, so `d2^R` factors through a
   projection of trace `1/m`. This recovers the proper-power ceiling.

This is a supplied deduction, not independent verification.
