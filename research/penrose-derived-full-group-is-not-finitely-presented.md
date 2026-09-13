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
- **Finite presentation forces finite type** (`zd-derived-full-group-fp-forces-finite-type`,
  landed by ex-fp-simple-relation-climbing, unreviewed). Expected dead for Penrose.
  - Mechanism: relators hold on configurations whose bounded windows are legal. So a
    configuration with legal small windows but an illegal large pattern violates a relation.
  - Why it should not fire: ChJN (arXiv:1602.04255, TeX lines 311–316, read on MSI) *define* a
    Penrose tiling as "a tiling of the whole plane by such rhombi, where markings of the edges
    match". Edge matching is a radius-1 rule. In the ambient of edge-marked rhombus tilings,
    legal radius-1 windows make the tiling a Penrose tiling, all of whose patterns are legal.
    The mechanism has nothing to act on, exactly as for Labbé's Wang shift.
  - Not verified:
    - the peer theorem is stated for `Z^d`-subshifts, and its adaptation to
      `Lambda = Z^2 ⊕ Z/5` was not checked;
    - whether ChJN's cut-torus action `Lambda ~ X` is conjugate to a `Lambda`-SFT. If it were
      not, and the theorem adapted, `D(𝒫)` would not be finitely presented. Local matching
      rules make that unlikely.
- **Matui's SFT-neighbourhood argument** (math/0404117). Superseded by the entry above: for a
  finite-type hull the neighbourhood is the hull itself.
- **LEF through periodic approximants.** Not attempted for Penrose.
  - The Labbé criterion `zd-subshift-full-group-lef-via-periodic-relator-shifts` is stated for
    `Z^d`-subshifts.
  - Rational approximants of the cut torus carry phason defects. By analogy with
    `labbe-lef-2026-09-12.md`, Section 4, slivers are expected to break relators.
- **Homology with nontrivial coefficients** (Bieri–Eckmann criterion for `FP_2`). Not attempted.
  Li's theorem reaches only coefficients pulled back from abelian covers.
