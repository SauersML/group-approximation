---
rg: 2
id: hs-full-rank-scalar-defect-no-go-proof
kind: route
title: Use a tiny nontrivial scalar and the neighbourhood-generation of the circle
target: hs-full-rank-scalar-defect-blocks-naive-rank-decoding
requires: []
artifacts:
  - research/artifacts/hs-to-rank-naive-decoder-no-go-2026-08-21.md
---

## Direct proof

Choose arbitrarily small `epsilon` with `epsilon/(2 pi)` irrational, put
`z=exp(i epsilon)`, and set `U=zI_d`.  Then

```text
||U-I||_2=|z-1| -> 0,       rank(U-I)/d=1.
```

A direct sum of copies has the same normalized rank.  A positive tensor power
is `z^r I_(d^r)` and irrationality ensures `z^r!=1`, so its defect from the
identity again has normalized rank one.  Also `ker(U-I)=0` and
`im(U-I)=C^d`, so retaining the
defect kernel keeps no carrier and quotienting by the defect image leaves the
zero space.  Random choice of vectors or subspaces cannot alter either exact
statement.

For the clipping assertion, let `c:U(1)->H` be multiplicative and suppose it
kills an open arc `N` around `1`.  Every `z in U(1)` has a sufficiently large
root `w` lying in `N`; then `c(z)=c(w)^r=1`.  Thus `c` is trivial.  A spectral
rule that clips every sufficiently small scalar phase to the identity cannot
simultaneously be multiplicative and retain any scalar phase separation.
