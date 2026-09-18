---
rg: 2
id: rational-breakpoint-dyadic-pl-groups-satisfy-boone-higman
kind: claim
title: Every finitely generated group of dyadic-slope piecewise linear homeomorphisms of the circle or interval with rational breakpoints embeds in a finitely presented simple group
distinct_from:
  pl-interval-and-circle-groups-have-type-a-orbit-actions: that is F(A,P) and T(A,P), whose breakpoints lie in the ring A; this allows breakpoints at non-dyadic rationals with slopes and translations still dyadic, which is not of the form F(A,P).
  periodic-germ-extensions-of-v-are-virtually-simple: that is the host; this is one family of groups that lifts into it.
---

**ESTABLISHED** by `rational-breakpoint-dyadic-pl-groups-satisfy-boone-higman-proof` (lane proof). *Reviewed:* gq-referee-a PASS (`research/artifacts/gq-referee-a-periodic-germ-extensions-of-v-and-breakpoint-consumers.md`, 135cfebbf), nits N1–N3 applied. No priority is claimed.

**Statement.**
- Let `PL_2(Q)` be the group of homeomorphisms of the circle `R/Z` that are piecewise of the form
  `θ ↦ 2^n θ + d`, with `n ∈ Z` and `d ∈ Z[1/2]`, with finitely many breakpoints, all rational.
- Then every finitely generated subgroup of `PL_2(Q)` embeds in the finitely presented simple group
  `G_Π'` of `periodic-germ-extensions-of-v-are-virtually-simple`, for a suitable `Π`.
- So it satisfies Boone--Higman. The same holds on `[0,1]`: those groups are the subgroups fixing `0`.

**The breakpoint condition is automatic.** Let `g` be a circle homeomorphism that is piecewise of
the form `θ ↦ 2^nθ + d`, with `d ∈ Z[1/2]` and finitely many pieces. At a breakpoint `s`, the map
`h = α_-^{-1}α_+ : θ ↦ 2^cθ + e` is a nontrivial circle map fixing `s`.
- If `c = 0`, then `h` is a dyadic rotation with a fixed point, hence the identity. That is
  excluded.
- So `c ≠ 0`, and `s(2^c - 1) ∈ Z[1/2]` modulo `Z`. Hence `s ∈ Q`.

So `PL_2(Q)` is the whole group of piecewise dyadic-affine homeomorphisms of the circle, and
**every finitely generated group of piecewise dyadic-affine homeomorphisms of the circle or of
`[0,1]` embeds in a finitely presented simple group.**

**Belk--Hyde--Matucci's example.** BHM (arXiv:2407.03149v1, §3.4, "Further examples", read at
source) take the group `G_S` of such maps with breakpoints in `Z[1/2] ∪ S`, where `S` is a
`T`-invariant set of non-dyadic rationals. They show that `G_S'` is simple and that `G_S/G_S'` is
free abelian of rank the number of `T`-orbits in `S`. They do not embed it in a finitely presented
simple group. This node puts every finitely generated subgroup of `G_S` into one. The lifting in the
proof needs only that the breakpoints lie in finitely many tail classes, not finite generation. So
when `S` is a finite union of `T`-orbits, `G_S` itself lifts into `G_Π`, and hence embeds in `G_Π'`.
