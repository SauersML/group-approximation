---
rg: 2
id: penrose-cut-torus-subshift-is-of-finite-type
kind: claim
title: The Penrose cut-torus action of Z^2 ⊕ Z/5 of Chornyi--Juschenko--Nekrashevych is conjugate to a free minimal subshift of finite type
distinct_from:
  circle-rotation-zd-codings-are-not-of-finite-type: That shows codings of circle rotations are never of finite type; this shows that the Penrose cut-torus action, a polygon exchange of a 2-torus with some irrational facet directions, is conjugate to a subshift of finite type, because Penrose matching rules are local.
  penrose-tiling-group-is-an-amenable-orbit-full-group: That imports the ChJN model and proves freeness and the invariant measure; this proves that the action is expansive and that the resulting subshift is of finite type.
  fp-alternating-full-groups-of-free-subshifts-force-sft: That proves that finite presentation of a derived full group forces finite type; this verifies finite type for the Penrose subshift, so that implication gives nothing against the Penrose group.
artifacts:
  - research/artifacts/penrose-cut-torus-sft-2026-09-16.md
---

**ESTABLISHED (unreviewed).**

**Setting.** As in `penrose-tiling-group-is-an-amenable-orbit-full-group`:
`Lambda = P/Lat ≅ Z^2 ⊕ Z/5` acts freely on the Cantor set `X = C~/Lat`, and the
Penrose tiling group is `𝒫 ≅ [[Lambda ~ X]]` (Chornyi--Juschenko--Nekrashevych,
arXiv:1602.04255).

**Statement.**
1. The action `Lambda ~ X` is expansive. For a suitable finite clopen partition of `X`,
   the itinerary map `X -> A^Lambda` is a `Lambda`-equivariant homeomorphism onto a
   free minimal `Lambda`-subshift `Y`.
2. `Y` is a subshift of finite type. Finite type is a conjugacy invariant, so every
   subshift conjugate to `Lambda ~ X` is of finite type.

**Consequences.**
- **Theorem G is silent for Penrose.** `fp-alternating-full-groups-of-free-subshifts-force-sft`
  holds over every infinite finitely generated group, including `Z^2 ⊕ Z/5`. If `D(𝒫)`
  is finitely presented, it forces `Y` to be of finite type, and `Y` is. So no
  finite-type obstruction can refute `penrose-derived-full-group-is-finitely-presented`.
  This settles the two points recorded as not checked in the Attempts of
  `penrose-derived-full-group-is-not-finitely-presented`: whether the theorem adapts to
  `Lambda`, and whether `Lambda ~ X` is conjugate to a `Lambda`-SFT. It also settles the
  finite-type question in the Attempts of `penrose-derived-full-group-is-finitely-presented`.
- **Class.** `Lambda ~ Y` is a free minimal SFT over a finitely generated abelian group,
  the same class as Labbé's `Omega_U` in `labbe-shift-derived-full-group-is-finitely-presented`.
- **Irrational facets** (artifact §5, Proposition 6, with exact determinants in
  `experiments/penrose-rational-directions-2026-09-16/`). Let `W ⊂ Q(ζ)` be any
  2-dimensional `Q`-subspace. Then one of the five facet directions `iζ^j R` meets `W`
  only in `0`.
  - So every torus `C/Lat'` with `Lat' ⊂ Q(ζ)`, including ChJN's `C/Lat`, has an
    irrational facet direction.
  - Hence `fp-simple-groups-have-no-rational-polytope-exchange-action` does not apply to
    these torus models.

**Trust surface.** The proof imports two statements that ChJN assert without proof. Line
numbers refer to their TeX source, fetched from arXiv on 2026-09-16.
- `V' ≅ 𝒯` is a homeomorphism (lines 485--500). ChJN attribute it to de Bruijn (1981),
  whose papers we did not fetch.
- `𝒯` is a Cantor set in the vertex-patch topology (lines 356--358), "from the properties
  of Penrose tilings". We use only that it is Hausdorff, which forces a Penrose tiling to
  be determined by its vertex set.

**Novelty.** The space of decorated Penrose rhombus tilings is of finite type by
definition. Fernique--Lutfalla (arXiv:2211.08239, abstract) prove the undecorated version,
which they describe as considered folk. What is new is only the transfer to ChJN's
`Lambda`-action. There `Lambda` is not a translation group of the tiling, so legal windows
must be developed into a plane tiling.

Proof: `penrose-cut-torus-subshift-finite-type-proof`.
