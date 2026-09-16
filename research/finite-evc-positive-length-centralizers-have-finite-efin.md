---
rg: 2
id: finite-evc-positive-length-centralizers-have-finite-efin
kind: claim
title: In a group with a finite E_VC model, centralizers of elements of positive homogeneous length are of type F_infinity with finite E_FIN quotients
distinct_from:
  finite-evc-unimodular-weyl-groups-have-finite-efin: that claim assumes unimodularity; this claim proves unimodularity for elements of positive length and applies it to concrete centralizers, products with Z and ascending HNN extensions
  bvc-bounds-conjugacy-classes-in-fibers-of-maps-to-z: that claim counts conjugacy classes in fibers of a map to Z under BVC; this claim derives finiteness properties of centralizers under a finite E_VC model
artifacts:
  - research/artifacts/finite-evc-commensurator-restriction-2026-09-16.md
---

**Statement.** Let `G` admit a finite model for `E_VC G`. Let `ℓ : G -> [0, ∞)` be conjugation
invariant with `ℓ(g^n) = |n| ℓ(g)`. Examples are:

- `|φ|` for a homomorphism `φ : G -> R`;
- `|ψ|` for a homogeneous quasimorphism `ψ`;
- the stable translation length of an isometric action.

If `ℓ(g) > 0`, then:

- (i) `N_G[<g>]` is unimodular, and `N_G[<g>] = N_G(<g^M>)` for some `M >= 1`;
- (ii) for every `k >= 1`, `Z_G(g^k)` has type `F_infinity` and `Z_G(g^k)/<g^k>` admits a finite
  `E_FIN` model.

**Corollaries.**

- **Products with `Z`.** If `Q × Z` has a finite `E_VC` model, then every centralizer `Z_Q(q)`
  has type `F_infinity` and a finite `E_FIN` model.
- **Ascending HNN extensions.** Let `G = <H, t | txt^{-1} = θ(x)>`, with `θ` an injective
  endomorphism of `H`, have a finite `E_VC` model. Then:
  - every twisted fixed subgroup `Fix(ι_h∘θ) = {x in H : hθ(x)h^{-1} = x}`, `h` in `H`, has
    type `F_infinity` and a finite `E_FIN` model;
  - the `θ`-periodic subgroup of `H` equals `Fix(θ^M)` for a single `M >= 1`, and it has type
    `F_infinity`.

  These constrain target (T2) of
  `research/artifacts/zp-vc-counterexample-candidates-2026-09-13.md`, in its finite-`E_VC`
  version. They were not found in the sources read, but they are elementary and may be
  folklore.

**Non-application.** In a torsion-free group with finitely many conjugacy classes, some
`c^a` is conjugate to `c^b` with `a < b`. So every stable length vanishes and every cyclic
commensurator is non-unimodular. This claim does not reach target (T1).
