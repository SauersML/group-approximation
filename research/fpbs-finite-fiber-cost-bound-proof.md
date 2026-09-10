---
rg: 2
id: fpbs-finite-fiber-cost-bound-proof
kind: route
title: Enlarge by fiber identifications and apply complete-section induction
target: fpbs-finite-fiber-cost-bound
requires:
  - fpbs-finite-index-star-relative-cost
  - fpbs-normalized-cost-induction-input
artifacts:
  - research/artifacts/fpbs/docs/finite-fiber-cost-descent.md
---

Section 1 enlarges the source orbit relation S to the pullback T
of the base relation, identifying every q-point fiber. Uniformity
makes T p.m.p. and base freeness gives [T:S]=q. The required
relative-cost repair gives C(T)<=C(S). A transversal of the finite
fibers is T-complete of measure 1/q and carries the base relation
with its original normalized measure. Induction gives
C(T)-1=(C(X)-1)/q. Lifting supplies the other inequality.

For an ergodic base with conditional atoms, the largest atom mass
a>0 and its multiplicity q are invariant base functions and hence
constants. The source set A of those largest atoms is invariant,
has measure qa, and with normalized measure is a uniform q-point
factor of X. Apply the proved bound to A->X and use invariant-piece
cost additivity to bound C(Y)-1 below by qa(C(A)-1). This yields
C(X)-1<=(C(Y)-1)/a when C(Y) is finite; the infinite-source case
is automatic. No claim of atomicity for arbitrary factors is made.

Section 2 proves the equivalence of the two universal equality
assertions without assuming either. For a subgroup H<=Gamma of
index q, the diagonal coset extension has cost
1+(C(a restricted to H)-1)/q, by induction on X x {H}.
Conversely write any uniform q-point extension using a permutation
cocycle, and let Gamma x Sym(q) act freely on X x Sym(q) by left
cocycle multiplication and commuting right multiplication. Its
subgroup Gamma x Stab(1) has index q. The two finite-fiber sections
carry the original base and source relations, with measures 1/q!
and 1/(q-1)!. The hypothesized index equality in that free action
therefore yields source/base equality. Only complete-section
induction is used unconditionally in this deduction.
