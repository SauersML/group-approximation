---
rg: 2
id: hilbert-hotel-block-cover-is-unconditional
kind: claim
title: The two-block Hilbert-hotel cover is a finitely presented Kazhdan group equal to its own MF radical, with no open leaf
distinct_from:
  hilbert-hotel-self-saturated-non-mf: that claim is the rank-20 `St_20` quotient built from the lifted Whitehead word and a rank-five transport, and its inputs were never discharged in Lean; this is the rank-16 two-block cover over `E_16(L_2(F_2))`, and every record it consumes is inhabited, so the endpoint carries no hypothesis at all.
  normal-kazhdan-defect-non-mf: that is the general engine -- a normal Kazhdan subgroup inside a compression defect forces full MF radical; this is one specific group for which every hypothesis of that engine is discharged unconditionally.
  torsion-free-finitely-presented-non-mf: that root asks for a TORSION-FREE finitely presented non-MF group; this group is not claimed torsion-free, and the Steinberg source carries torsion.
artifacts:
  - GroupApproximation/Leavitt/HilbertHotelCoverBlock.lean
  - GroupApproximation/Leavitt/HilbertHotelEndpoint.lean
  - GroupApproximation/Leavitt/ConjProductClosure.lean
---

There is a **finitely presented** group `G` with

```text
G is Kazhdan, countable, nontrivial,
every element of G is corona-MF-invisible,
G is not operator MF,
cdeMFResidual G = top.
```

and the proof of this carries **no hypothesis**: it is
`HilbertHotel.CoverBlock.exists_finitelyPresented_kazhdan_full_mf_radical`,
whose witness is `HilbertHotel.CoverBlock.HotelGroup`, the two-block Shalom
cover of the model `E_16(L_2(F_2))`.

The two records the construction is stated against are both inhabited:
`blockCoverInputs` from `HilbertHotel.Cover.coverInputs_nonempty`, and
`coverBlockResiduals` from the four model-level facts of the block layer.  The
block file's own "Open leaves" section reads "None."

## Why the two-block cover and not the one-block one

This is the point of the claim, and it is a structural fact rather than a
matter of effort.  The one-block cover `Cover.CoverGroup C` cannot be finished:
its `CoverResiduals` record has nine fields, six are discharged, and the three
that are not cannot be, because the Kazhdan source `Gamma = E_4(R)` maps into
the *model* and the covering map runs `CoverGroup ->> Model`, the wrong way to
carry it upstairs.  That is
[[one-block-cover-residuals-are-structurally-unreachable]].

The two-block construction answers exactly that: it puts the corner *inside*
the presentation, so the Kazhdan source lands in the cover by construction and
nothing has to be pulled back along a surjection.

## What is not claimed

Not torsion-freeness, and not non-soficity of `HotelGroup` --- the companion
[[hilbert-hotel-model-is-unconditionally-non-mf]] records non-soficity for the
*model*, which is only finitely generated.  The split between the two groups is
deliberate: the finitely presented endpoint and the concrete matrix-group
endpoint are different groups, and neither carries both properties.
