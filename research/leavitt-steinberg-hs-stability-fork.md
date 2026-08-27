---
rg: 2
id: leavitt-steinberg-hs-stability-fork
kind: claim
title: The Leavitt--Steinberg normalized-HS stability fork
distinct_from:
  wreath-flexible-hs-stability: That is an open stability claim for the wreath candidate; this is an established conditional dichotomy for the Leavitt--Steinberg cover.
  non-hyperlinear-group: This theorem gives a nonhyperlinear group only on its stable branch; it does not select that branch.
  hyperlinear-nonsofic-group: This theorem gives a hyperlinear nonsofic quotient only on its unstable branch; it does not select that branch.
  leavitt-steinberg-hs-stable: This is the proved implication for either outcome; the other selects the stable outcome.
  leavitt-steinberg-hs-unstable: This is the proved implication for either outcome; the other selects the unstable outcome.
artifacts:
  - notes/ATLAS_HS_CRITERION.md
  - notes/NON_MF_TO_HYPERLINEAR_DIFFERENTIAL_AUDIT.md
  - notes/NOTEPAD.md
---

Put `L=L_(F_2)(1,2)`, `U=St_5(L)`, and `Q=EL_4(L)`.  Exactly one of the
following branches holds:

- if `U` is normalized Hilbert--Schmidt stable, then `U` is nonhyperlinear;
- if `U` is not normalized Hilbert--Schmidt stable, then a central quotient
  of `U` is hyperlinear and nonsofic (and central-quotient permanence makes
  the already nonsofic group `Q` hyperlinear).

The inputs are finite presentability and minimal almost periodicity of `U`,
quasisimplicity of `U`, and nonsoficity of the relevant central quotients.
The fork is unconditional, but it does not decide which branch occurs.
