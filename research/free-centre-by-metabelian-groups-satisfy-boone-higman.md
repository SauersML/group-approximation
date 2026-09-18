---
rg: 2
id: free-centre-by-metabelian-groups-satisfy-boone-higman
kind: claim
title: The finite-rank free centre-by-metabelian groups F/[F'',F] lie in the permutational Boone--Higman class
distinct_from:
  product-variety-free-groups-satisfy-permutational-boone-higman: that is free groups of products of abelian varieties, reached by Magnus-type wreath embeddings; this is the centre-by-metabelian variety, whose free groups are central extensions of free metabelian groups and have no such embedding recorded.
  free-solvable-groups-satisfy-permutational-boone-higman: that is F/F^(d); this is F/[F'',F], a central quotient between F/F''' and F/F''.
---

**OPEN for r >= 3; rank 2 settled** by `free-centre-by-metabelian-group-of-rank-two-satisfies-pbh` (lane proof, 2026-09-18).

**OPEN.** For every finite `r >= 2`, the free centre-by-metabelian group
`C_r = F_r/[F_r'', F_r]` lies in `B_A`. Then all its subgroups embed in finitely
presented simple groups.

## Why it is the first uncovered named case

- `C_r` is solvable of derived length at most 3. It is a central extension
  `1 -> F''/[F'',F] -> C_r -> M_r -> 1` of the free metabelian group `M_r`, which is
  in `B_A`.
- It is not of the form `F/[N,N]N^m` over any quotient. Its centre-by-metabelian
  law is `[[[x,y],[z,w]], u]`, not a product of abelian laws. So
  `product-variety-free-groups-satisfy-permutational-boone-higman` does not apply.
- **Torsion.** Per the abstract of C. K. Gupta, "The free centre-by-metabelian groups"
  (J. Austral. Math. Soc., 1973), as returned by a web search, `C_n` contains an
  elementary abelian 2-group for `n >= 4`. The paper itself was not read.
  - Torsion does not obstruct `B_A` membership, since finite groups are in `B_A`.
  - It does show that `C_r` is not torsion-free, so a torsion-free linear host is
    ruled out.

## Attempts

1. **Magnus-type embedding.** *Not available.* The Magnus and exponent-`m`
   embeddings (`magnus-embedding-mod-m-into-wreath-product`) only produce quotients by
   verbal subgroups of the form `[N,N]N^m`.
2. **Central extensions.** *Blocked by an open closure question.* Membership would
   follow if `B_A` were closed under central extensions by finitely generated abelian
   groups, whenever the extension has solvable word problem. No such closure is on
   main. The Deligne-lattice node shows that central extensions of `B_A` groups
   (`Sp_4(Z)`) are a live difficulty.
3. **Quasi-linearity.** *Not checked.* Whether `C_r` is linear over a finite product of
   fields was not pinned. Every finitely generated quasi-linear group is residually
   finite, so a failure of residual finiteness would rule this route out. Residual
   finiteness of `C_r` was not checked either.
4. **Untested.** Embedding `C_r` in a central extension of `Z^r wr M_r` realised
   inside a type (A) actor, e.g. as a subgroup of a relative automorphism actor with a
   central lamp.
5. **Second-order Magnus embedding (bh-free-28, 2026-09-18).** *Settles r = 2; reduces r >= 4.*
   - Attempt 1's "not available" is superseded at rank 2. The 4x4 block matrices
     `[[1,a,c],[0,gI,b],[0,0,1]]` over `Z[x^(±1),y^(±1)]` give a faithful representation of
     `C_2` (`free-centre-by-metabelian-group-of-rank-two-is-linear`), so `C_2` is in `B_A`
     through the characteristic-zero linear node.
   - For `r >= 4`, `C_r` is linear, hence in `B_A`, exactly when it is residually finite
     (`free-centre-by-metabelian-groups-linear-iff-residually-finite`, using Gupta 1973 at
     abstract level).
   - Rank 3 and residual finiteness for `r >= 4` remain open. Classical priority: C. K. Gupta
     (1969, 1973) gives faithful 3x3 representations in this family; not read.

_Orphan sweep (2026-09-14): this node cited `research/artifacts/bh-solvable-general-2026-09-13.md`, which its lane never wrote to the repository and which could not be recovered from the lane transcript._
