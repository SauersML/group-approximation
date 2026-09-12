---
rg: 2
id: leavitt-d4-l14-i1412-corrected-eq3-retraction-skeleton-proof
kind: route
title: Multiply the corrected carrier syllables separately in each free factor
target: leavitt-d4-l14-i1412-corrected-eq3-retraction-skeleton
requires:
  - leavitt-d4-l14-six-winner-profile-has-two-classes
---

Read the corrected `COLORS` and `S` arrays in parallel.  For each color
`c`, delete every syllable of a different color and multiply the remaining
coefficient words in their original order.  Colors three, two, one, and
zero give `R3`, `R2`, `R1`, and `R0`, respectively.  These are necessary
relations for the full free-product word to be the identity because each
copy retraction is a homomorphism.

The abelianization of a presentation with twelve generators and these four
relators is the cokernel of a homomorphism from `Z^4` to `Z^12`; its free
rank is at least `12-4=8`.  Hence the retraction skeleton admits nontrivial
coefficient specializations and cannot by itself prove a one-copy boundary
fence.  A valid fence must use the finer noncrossing cancellation blocks,
not only the four retractions.

