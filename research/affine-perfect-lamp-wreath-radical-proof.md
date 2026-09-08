---
rg: 2
id: affine-perfect-lamp-wreath-radical-proof
kind: route
title: Discharge the conditional wreath family at the level-three affine congruence base
target: affine-perfect-lamp-wreath-has-locally-finite-mf-radical
requires:
  - kazhdan-self-embedding-has-sofic-perfect-lamp-non-mf-family
  - affine-congruence-source-is-kazhdan
artifacts:
  - research/artifacts/affine-perfect-lamp-wreath-recheck-2026-09-08.md
---

The family claim is stated for a countable residually finite
property-`(T)` group with a proper finite-index injective endomorphism,
plus residual finiteness of the ascending HNN extension for the radical
equality. The prerequisite arithmetic claim supplies the first three:
`P=Gamma(3) ltimes Z^3` is finitely presented with property `(T)`, and
`alpha(g,v)=(g,2v)` is injective with image `Gamma(3) ltimes 2Z^3` of
index `8`, with `(1,e_1)` outside it. `P` is residually finite as a
finitely generated linear group over `Z`.

The remaining hypothesis is residual finiteness of `H`. The affine
model displayed in the target embeds `H` in `GL_4(Z[1/2])`, and
conjugation by `t` sends `[[A,v],[0,1]]` to `[[A,2v],[0,1]]`, which is
`alpha`; the height `h` retracts `H` onto `Z` with kernel
`Gamma(3) ltimes Z[1/2]^3 = union_(n>=0) t^-n P t^n`, so the model is
the ascending HNN extension and not a proper quotient of it. `H` is a
finitely generated subgroup of `GL_4(Q)`, so Malcev gives residual
finiteness. Explicitly, reduction of `Z[1/2]` modulo an odd `q` is
defined, and a nonidentity element has some entry of `2^h A-I` or of
`v` with nonzero image for all large odd `q`.

With `B=A_5`, nontrivial and perfect, the family claim then applies
verbatim and gives soficity, failure of MF, and
`Rad_MF(W)=D_W(L)=A_5^(X)`. Local finiteness of `A_5^(X)` is immediate
from the restricted direct sum: a finite subset of coordinates generates
a subgroup of a finite power of `A_5`. Infinitude is the infinitude of
`X=H/L`, which follows from the height map, since `t^-n P t^n` is
strictly increasing. This last point is what separates the conclusion
from `finite-block-perfect-lamps-have-exact-mf-radical`, whose radical
is a free product of finite groups and contains a free group of rank
two.
