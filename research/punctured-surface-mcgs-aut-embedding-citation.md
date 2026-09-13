---
rg: 2
id: punctured-surface-mcgs-aut-embedding-citation
kind: route
title: Import the embedding steps of the proof of Corollary B of Belk--Fournier-Facio--Hyde--Zaremsky
target: punctured-surface-mcgs-virtually-embed-in-aut-free-groups
requires: []
artifacts:
  - research/artifacts/bh-out-fn-closed-mcg-2026-09-12.md
---

Citation import, not a reproof. Belk--Fournier-Facio--Hyde--Zaremsky,
arXiv:2503.21882v2, Section 4, proof of Corollary B ("The (extended) mapping
class group of an orientable surface Σ of finite type, where Σ either has
non-empty boundary, at least one puncture, and/or genus at most two"). Read on
2026-09-13 from the arXiv HTML render through an extraction tool; the same steps
were read from the PDF on MSI on 2026-09-12 and are quoted in §2 of
`research/artifacts/bh-out-fn-closed-mcg-2026-09-12.md`.

1. **At least two punctures.** "MCG(Σ,∗) embeds into Aut(π₁(Σ)) by the
   Dehn–Nielsen–Baer Theorem" [FM12, Theorem 8.8]. Here one puncture is treated as
   the marked point `∗`, `π₁(Σ)` is free because `Σ` still has a puncture, and
   `MCG(Σ, ∗)` has finite index in the mapping class group of the punctured
   surface.
2. **One puncture.** A finite-index `L` lifts to a double cover `Σ̃` with two
   punctures: "Each element in L has a unique lift that fixes the two punctures in
   Σ̃. This defines a homomorphism L→MCG(Σ̃), which is injective by a version of
   the Birman–Hilden Theorem" [ALS09, Corollary 4]. The image fixes both punctures,
   so step 1 applies to it.
3. **Boundary.** Attaching punctured disks to the boundary components gives a
   surface `Σ′`, and "MCG(Σ) embeds into MCG(Σ′)" [FM12, Theorem 3.18]; step 1 or 2
   applies to `Σ′`.
4. **Orientation.** The orientation-preserving subgroup has index at most 2 in
   the extended group.

Composing the injective homomorphisms on finite-index subgroups gives the claim.
What BFFHZ derive from these steps for the Boone--Higman property is not imported
here. [FM12] is Farb--Margalit, *A Primer on Mapping Class Groups*; [ALS09] is
Aramayona--Leininger--Souto, arXiv:0811.0841. Their theorem statements were not
re-read here.
