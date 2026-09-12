---
rg: 2
id: terminated-digit-boundary-sets-have-prefix-transport
kind: claim
title: Finite unions of digit boundary tiles with the same residue admit supported prefix transport
artifacts:
  - research/artifacts/boone-higman-enlarged-digit-fiber-stabilizer-2026-09-08.md
---

Use the terminated-digit graph with h>=2,r>=2, and put
T={1,...,h}^N in C_Y. A boundary tile is alpha*T for a finite
path alpha starting at X and ending at Y. A boundary set is a
finite disjoint union of such tiles. Include the empty set.

For a boundary set A, its tile count modulo h-1 is well defined;
write b(A) for this residue and use b(empty)=0. Boundary sets are
closed under finite unions, intersections, and differences. Every
element of H_(h,r) maps boundary sets to boundary sets and preserves b.

If nonempty boundary sets A,A' lie in a clopen D and satisfy
b(A)=b(A'), there is a canonical prefix homeomorphism supported in
D taking A onto A'. In particular the transport belongs to H_(h,r).
The empty set is transportable only to the empty set.

For this existence statement D may be all of C_X. If both sets
are disjoint from F=union_i i*T, D may instead be chosen clopen
and disjoint from F, so the transport fixes F pointwise.
