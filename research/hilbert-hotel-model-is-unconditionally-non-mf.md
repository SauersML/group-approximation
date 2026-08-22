---
rg: 2
id: hilbert-hotel-model-is-unconditionally-non-mf
kind: claim
title: The explicit matrix group E_16 over the binary Leavitt algebra is unconditionally non-sofic, non-MF, and equal to its own MF radical
distinct_from:
  hilbert-hotel-block-cover-is-unconditional: that claim is about the finitely presented two-block cover; this is about the model it covers, which is an explicit matrix group but only finitely generated, so the two endpoints are different groups with different profiles.
  hilbert-hotel-self-saturated-non-mf: that is a rank-20 Steinberg quotient whose inputs were never formalized; this is a concrete rank-16 elementary matrix group over a named ring, with every step in the kernel.
  normal-kazhdan-defect-non-mf: that is the general engine; this is the instance in which its every hypothesis is met by a group written down in coordinates.
artifacts:
  - GroupApproximation/Leavitt/HilbertHotelModelNonMF.lean
  - GroupApproximation/Leavitt/HilbertHotelEndpoint.lean
  - GroupApproximation/Leavitt/HilbertHotelDefectNormal.lean
---

Let `R = L_(F_2)(1,2)` be the binary Leavitt algebra and

```text
Model := EL_16(R),
```

the elementary subgroup of `GL_16(R)`, an explicit matrix group.  Then,
unconditionally:

```text
Model is Kazhdan, finitely generated, infinite, nontrivial,
Model is not sofic,
Model is not operator MF,
coronaMFResidual Model = normMFResidual Model = cdeMFResidual Model = top.
```

Every declaration is hypothesis-free: `Cover.not_isOperatorMF_model`,
`Cover.cdeMFResidual_model_eq_top`, `Endpoint.model_not_isSofic`,
`Endpoint.model_full_profile`.  Nothing is stated relative to `CoverInputs` or
`CoverResiduals`.

The compression core is `Cover.modelCore`: `iota` is the corner embedding of
`Gamma = E_4(R)` into the `16`-frame, the stable letter is `tauModel`, the mark
is `markModel = e_45(1)`, and the defect is `e_02(q)` with `q = s_1 t_1`.  Its
two compression clauses are proved directly from the block layer, and the
defect normally generates the whole model, so the normal Kazhdan subgroup can
be taken to be `top`.

## What this does and does not settle

It settles the **analytic** half outright: the obstruction needs no covering
group, no imposed relator, and no open record.  What it does not give is
**finite presentability** --- `Model` is finitely generated and nothing here
presents it finitely.  That is precisely why the cover layer exists, and the
finitely presented endpoint is the separate group of
[[hilbert-hotel-block-cover-is-unconditional]].

Read the pair as one two-group split rather than as one theorem: the concrete
matrix endpoint is finitely generated, and the finitely presented endpoint is
not concrete.
