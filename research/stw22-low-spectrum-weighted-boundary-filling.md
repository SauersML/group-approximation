---
rg: 2
id: stw22-low-spectrum-weighted-boundary-filling
kind: claim
title: Extend low-spectrum weighted boundary frames without polar continuity
---

Let `R` be the hyperfinite `II_1` factor, let `e in R` be a projection, and
fix `s<tau(e)`.  There is a modulus with the following property, uniformly
for positive contractions `a` with `tau(supp(a))<=s`.

After a spectral split `a=a_h+a_l`, with `a_l<=eta`, suppose a high-frame
loop has been filled over a disk and the continuous boundary low weighted
frames are orthogonal to the high frame.  Then those weighted frames extend
over the disk, remain orthogonal to the high frame, and stay within
`2 sqrt(eta s)` of a fixed low weighted frame.

The boundary polar frames are not assumed continuous in ordinary `2`-norm.
This weighted relative extension is the remaining cross-stratum hinge for
transferring the proved strong-Stiefel loop modulus to weighted purification
fibres.

## Attempts

The ordinary polar-frame route fails exactly at zero spectrum: continuity
of `v(z)a_l^(1/2)` does not control `v(z)supp(a_l)` in `2`-norm.  Spectral
truncation repairs every fixed positive cut, but passing the fillings to the
limit while preserving the exact boundary and orthogonality to a moving
high frame has not been justified.  A successful attack must work directly
in the weighted low fibre, or prove a relative limit theorem for these
truncated fillings.
