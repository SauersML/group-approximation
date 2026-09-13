---
rg: 2
id: penrose-derived-full-group-is-not-finitely-presented
kind: claim
title: The derived subgroup of the Penrose tiling full group is not finitely presented
invalidates:
  - fp-simple-amenable-orbit-via-penrose-group
  - fp-simple-irs-via-penrose-group
distinct_from:
  penrose-derived-full-group-is-finitely-presented: That is the positive claim; this is its negation. When this claim is established it should be named in that claim's refuted_by, and it kills the two Penrose routes to the orbit-certificate and IRS claims.
  penrose-derived-full-group-homology-is-finitely-generated: That proves the homological obstruction to this claim vanishes; this is the negation itself, still open.
---

**OPEN.** `D(𝒫)` is not finitely presented. Here `𝒫` is the Penrose tiling group of
Chornyi–Juschenko–Nekrashevych (`penrose-tiling-group-is-an-amenable-orbit-full-group`).

**Why it matters.** `D(𝒫)` is a finitely generated infinite simple sofic group. A proof would
settle `penrose-derived-full-group-is-finitely-presented` negatively. It would also invalidate
`fp-simple-amenable-orbit-via-penrose-group` and `fp-simple-irs-via-penrose-group`, leaving
Labbé's shift as the only recorded tiling instance of the orbit certificate for
`hyperlinear-fp-infinite-simple-group`.

## Attempts

- **Infinitely generated homology.** Dead:
  `penrose-not-fp-via-infinitely-generated-homology`, invalidated by
  `penrose-derived-full-group-homology-is-finitely-generated`. `H_2(D(𝒫)) ≅ Z ⊕ T` with `T`
  finite, and every `H_j` is finitely generated.
- **Additive invariant-measure relation invariants** (mean signed area of relator loops, or any
  conjugation-invariant homomorphism on the relation subgroup). Dead:
  `penrose-not-fp-via-mean-area-relation-invariant`. They factor through `N/[F,N]`, which is
  finitely generated.
- **Matui's SFT-neighbourhood argument** (math/0404117). Not adapted.
  - Penrose tilings obey local matching rules, so, as for Labbé's shift, the hull should be its
    own finite-type neighbourhood. That would leave the argument no room.
  - We did not check from a source that the ChJN coding is of finite type.
- **LEF through periodic approximants.** Not attempted for Penrose.
  - The Labbé criterion `zd-subshift-full-group-lef-via-periodic-relator-shifts` is stated for
    `Z^d`-subshifts.
  - Rational approximants of the cut torus carry phason defects. By analogy with
    `labbe-lef-2026-09-12.md`, Section 4, slivers are expected to break relators.
- **Homology with nontrivial coefficients** (Bieri–Eckmann criterion for `FP_2`). Not attempted.
  Li's theorem reaches only coefficients pulled back from abelian covers.
