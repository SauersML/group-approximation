---
rg: 2
id: spherical-artin-groups-satisfy-boone-higman
kind: claim
root: true
title: Every spherical-type Artin group embeds in a finitely presented simple group
distinct_from:
  spherical-artin-boone-higman-reduces-to-e6-e7-e8: that is the established conditional statement reducing the permutational form to E_6, E_7, E_8; this is the open unconditional Boone--Higman statement for all spherical types, which that reduction feeds as one route.
  artin-groups-satisfy-boone-higman: that is the open named problem over all Artin groups with solvable word problem; this is its spherical part.
  spherical-artin-groups-are-linear-over-q-x-y: that is the established linearity of these groups over Q(x,y); this asks for a finitely presented simple envelope, which linearity gives only through the open characteristic-zero root.
artifacts:
  - research/artifacts/bh-artin-groups-2026-09-12.md
---

**OPEN.** Every Artin group of spherical type embeds in a finitely presented
simple group.

*Marked `root` because it is a named open class.* BFFHZ (arXiv:2503.21882v2,
after Corollary B) and survey Remark 5.4 both list the exceptional spherical
types as open.

**Status.**
- **Settled types:** A_n, B_n = C_n, D_n and I_2(m), in the permutational form
  (`aut-free-groups-satisfy-permutational-boone-higman`).
- **Open types:** BFFHZ and survey Remark 5.4 keep the exceptional types open.
  Those are E_6, E_7, E_8, F_4, H_3 and H_4 (G_2 = I_2(6) is dihedral).

**Routes.**
1. `spherical-artin-bh-via-char-zero-linear-groups`: these groups are linear
   over `Q(x,y)` (`spherical-artin-groups-are-linear-over-q-x-y`), so the claim
   follows from the open root `char-zero-linear-groups-satisfy-boone-higman` at
   transcendence degree 2.
2. `spherical-artin-bh-via-e-type-reduction`: by
   `spherical-artin-boone-higman-reduces-to-e6-e7-e8`, it suffices that
   E_6, E_7, E_8 satisfy the permutational property
   (`e-type-artin-groups-satisfy-permutational-boone-higman`).

## Attempts

1. **Mapping class groups with boundary.** *Dies for the E types.* Paris
   (arXiv:0711.2372, §7.1): "the representation ρPV is faithful if and only if
   either Γ = An for some n≥ 1, or Γ = Dn for some n≥ 4". So the geometric
   monodromy does not put E_6, E_7, E_8 inside a mapping class group of a surface
   with boundary, where BFFHZ would apply.
2. **Zaremsky's rational theorem.** *Does not reach.* The faithful LKB
   representation lives over `Q(x,y)`. No faithful specialization to a number
   field is recorded in the sources read. `algebraic-linear-groups-satisfy-boone-higman`
   covers only transcendence degree zero.
3. **Locally finite trees.** *Dies.* Irreducible spherical Artin groups have
   infinite centre. Jankiewicz (arXiv:2103.01343) notes that none of them splits
   as a graph of finite-rank free groups except the dihedral ones, so the BLIW
   generalized Baumslag--Solitar route does not apply.
