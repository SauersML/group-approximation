---
rg: 2
id: central-one3-tag-sections-force-source-affine-safety
kind: claim
title: Scalar ONE3 tag sections force affine safety of the lifted source support
distinct_from:
  fano-cap-witness-sections-force-source-affine-safety: that uses the Fano-cap geometry of R-star; this uses the two explicit affine fibers of positive one-in-three.
  central-tagged-one-in-three-is-a-finite-lcs-or: that lowers an already central-tagged target instance; this constrains when a classical completeness reduction can produce such central tags.
---

ESTABLISHED.
Let a pp-gadget over positive ONE3 encode a visible relation `C`, and let
`S subseteq C` be the positive support of a source perfect trace.  Choose one
satisfying target witness `sigma(phi)` for every `phi in S`.  Designate one
coordinate `t_j` in each target ONE3 occurrence `j`.

If `t_j` is constant on `sigma(S)` for every `j`, then there is an affine
relation `A` with

```text
S subseteq A subseteq C.                                       (OTS1)
```

Indeed, fixing the designated ONE3 coordinate selects one of the affine
fibers in `(CTO2)`.  Replace every target clause by its selected affine
fiber.  The simultaneous solution set is affine, contains all chosen
witnesses, and is contained in the original gadget.  Visible projection
gives `(OTS1)`.

In particular, if `S=C` and `C` is nonaffine, no completeness section can
make one designated tag in every target clause scalar.  More generally the
necessary condition is

```text
Aff(S) subseteq C.                                             (OTS2)
```

Thus a constraintwise Culf--Mastel lift cannot create the central tags of
`central-tagged-one-in-three-is-a-finite-lcs-or` on a full nonaffine source
support.  The remaining escape is the same source-specific one exposed by
the Fano analysis: a proper affine-safe HALT support or a genuinely global
contextual construction not arising from a witness section.
