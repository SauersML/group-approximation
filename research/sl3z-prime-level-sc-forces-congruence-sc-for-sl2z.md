---
rg: 2
id: sl3z-prime-level-sc-forces-congruence-sc-for-sl2z
kind: claim
title: Prime-level strong convergence for SL_3(Z) forces the full mean-zero congruence regular representations of SL_2(Z) to converge strongly
artifacts:
  - research/artifacts/sl3z-prime-level-witness-completeness-2026-09-13.md
distinct_from:
  cubic-division-congruence-sc-descends-to-thin-subgroups: that transfers strong convergence of the canonical l^2_0(SL_3(F_p)) of a division-algebra lattice to its thin subgroups; this starts from an arbitrary irreducible sequence of SL_3(Z) and shows that on the block SL_2 it already has the norms of the full l^2_0(SL_2(F_p)).
---

ESTABLISHED (unreviewed).  Let `rho_i` be irreducible representations of
`SL_3(F_(p_i))`, pulled back to `SL_3(Z)`, with `rho_i -> lambda_(SL_3(Z))`
strongly.  Then `l^2_0(SL_2(F_(p_i))) -> lambda_(SL_2(Z))` strongly, where the
block `SL_2(Z)` acts through reduction mod `p_i`.  So the Sanov Cayley graphs
`Cay(SL_2(F_(p_i)), {[[1,+-2],[0,1]], [[1,0],[+-2,1]]})` are asymptotically
Ramanujan, with largest nontrivial eigenvalue tending to `2 sqrt 3`.  The same
holds for every element of `C[F_2]`, giving explicit deterministic strong
convergence for a free group, which van Handel (arXiv:2510.12520, Section 2.2)
records as open.

The key point is that there is no selection freedom.  Each cuspidal constituent
of `SL_3(F_p)` restricts to the block `SL_2(F_p)` with every nontrivial irreducible
representation of `SL_2(F_p)`, with multiplicity `dim sigma - dim sigma^U`, or a
third of that for cubic-twist constituents.  By
`sl3z-prime-level-invariant-witnesses-are-complete` only cuspidal constituents
survive.  So at prime levels a positive answer to
`sl3z-purely-matricial-field` contains the Ramanujan property for all group-ring
elements of the prime congruence quotients of `SL_2(Z)`.  Conversely, one
persistent outlier in those Cayley graphs refutes prime-level strong
convergence for `SL_3(Z)`.  At squarefree levels the analogous upper bound holds
for the new-at-`C_i` parts `(x)_(p in C_i) l^2_0(SL_2(F_p))`, where `C_i` is the
set of cuspidal prime factors.

Proof: `sl3z-prime-level-sc-forces-congruence-sc-for-sl2z-proof`.
