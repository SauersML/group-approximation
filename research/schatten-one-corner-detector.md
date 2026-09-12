---
rg: 2
id: schatten-one-corner-detector
kind: claim
title: Unnormalized Schatten-one models retaining a central radical involution give a detector
distinct_from:
  radical-collision-criterion: That established claim turns a detector into a hyperlinear nonsofic group; this one manufactures the detector itself from an unnormalized Schatten-one model, and is where the corner renormalization happens.
  corner-renormalization-cost: That claim is the general norm bookkeeping; this one is the group-level consequence in the unnormalized Schatten-one case.
artifacts:
  - notes/TRUE_SCHATTEN_ONE_RADICAL_CORNER.md
---

Let `E` be countable with `z != 1`, `z^2=1`, `z` central and
`z in Rad_sof(E)`.  Suppose there are maps `phi_n : E -> U(d_n)` with

```text
||phi_n(gh)-phi_n(g)phi_n(h)||_1 -> 0   (g,h in E),
liminf_n ||phi_n(z)-1||_1 > 0,
```

in the *unnormalized* Schatten-one norm.  Then the image of `E` in a tracial
matrix ultraproduct built from the negative spectral corner of `z` is
hyperlinear, retains `z`, and is therefore nonsofic: a hyperlinear nonsofic
group exists.

Neither hyperlinearity of `E/<z>` nor a positive-density negative
`z`-spectral sector is needed.  The reason is the scaling boundary of
`corner-renormalization-cost` read in the favourable direction: a nonzero
corner has rank at least one, so an *unnormalized* trace-norm error becomes a
normalized Hilbert--Schmidt error in the corner with no density loss
(`||A||_(2,r)^2 <= 2||A||_1/r <= 2||A||_1`).  There is no analogue for a
normalized Schatten-one or normalized Hilbert--Schmidt model, where the whole
error may concentrate on the selected `o(d_n)` corner.
