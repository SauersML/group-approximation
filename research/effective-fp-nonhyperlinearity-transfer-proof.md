---
rg: 2
id: effective-fp-nonhyperlinearity-transfer-proof
kind: route
title: Instantiate the transfer modulus at the Chornomaz-Wagner host
target: effective-fp-nonhyperlinearity-transfer
requires:
  - quantitative-higman-embedding-with-dehn-control
  - subgroup-dehn-function-is-the-hyperlinearity-modulus
---

`quantitative-higman-embedding-with-dehn-control` supplies, for each `eps>0`, a
finitely presented `H_eps` containing `G` with bounded distortion and with
relative Dehn function `delta_(G,H_eps)(n) <= T(n)^(2+eps)`.

**(EFT1).**  Hyperlinearity passes to subgroups: an injective homomorphism
`H_eps -> U(R^omega)` restricts to one on `G`.  So `H_eps` hyperlinear would
make `G` hyperlinear, and the contrapositive is the claim.  (This step uses
nothing from the two prerequisites; it is recorded here because the composite
statement contains it.)

**(EFT2).**  Substitute `delta_(G,H_eps)(n) <= T(n)^(2+eps)` into `(SDM3)` of
`subgroup-dehn-function-is-the-hyperlinearity-modulus`, whose hypothesis is
exactly that `H_eps` be finitely presented with finite relative Dehn function.

**(EFT3).**  For quasilinear `T`, `T(n)^(2+eps)` is `n^(2+eps)` up to the
complexity preorder.  The lower bound is the source's own remark: a
non-hyperbolic `G` admits no bounded-distortion embedding into a hyperbolic
group, so by Gromov's isoperimetric gap as proved by Ol'shanskii, the Dehn
function of `G` in any finitely presented host is at least quadratic when the
embedding is quasi-isometric.  The source notes this last form of the gap is
not a direct consequence of the classical statement but follows along the same
lines as Ol'shanskii's proof; it is imported at that strength and no stronger.
