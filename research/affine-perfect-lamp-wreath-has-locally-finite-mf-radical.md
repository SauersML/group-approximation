---
rg: 2
id: affine-perfect-lamp-wreath-has-locally-finite-mf-radical
kind: claim
title: An explicit sofic non-MF ordinary wreath product whose MF radical is an infinite locally finite perfect group
distinct_from:
  kazhdan-self-embedding-has-sofic-perfect-lamp-non-mf-family: that states the family conditionally over an unnamed residually finite Kazhdan base and declines to import a concrete one; this discharges every one of its hypotheses at the level-three affine congruence group, so the sofic non-MF conclusion and the radical computation are unconditional, and it records that the resulting radical is locally finite.
  finite-block-perfect-lamps-have-exact-mf-radical: that is the finitely presented free-product-of-finite-blocks construction, whose radical contains a free group of rank two and so is not locally finite; this is the ordinary restricted permutational wreath product, which is not finitely presented and whose radical is locally finite.
  wreath-compression-mf-radical: that is the general lamp-family radical computation, covering abelian lamps and running through two-point fibers and torsion collapse; this is one explicit perfect-lamp group over an index-eight affine compression, obtained from the commuting-conjugate centralizer criterion.
  affine-congruence-source-is-kazhdan: that is the arithmetic input, a property-(T) torsion-free source with a proper finite-index self-embedding; this is the wreath product built over it and the computation of its MF radical.
artifacts:
  - research/artifacts/affine-perfect-lamp-wreath-recheck-2026-09-08.md
  - research/artifacts/compression-locally-finite-centralizer-criterion-2026-09-08.md
---

Let `P = Gamma(3) ltimes Z^3` be the level-three affine congruence
group of `affine-congruence-source-is-kazhdan`, and let
`alpha(g,v)=(g,2v)`, injective with image of index `8`. Realize the
ascending HNN extension faithfully in `GL_4(Z[1/2])`:

```text
H = { [[2^h A, v],[0,1]] : h in Z, A in Gamma(3), v in Z[1/2]^3 },
t = [[2I,0],[0,1]],     L = P,   u = t,   X = H/L,
W = A_5^(X) semidirect H.
```

Then `uLu^-1 = alpha(P) < L` properly, `ell=(1,e_1)` lies in `L` outside
`uLu^-1`, and `H` is residually finite. The group `W` is countable and
sofic, is not MF, and

```text
Rad_MF(W) = D_W(L) = A_5^(X),      W/Rad_MF(W) ~= H,
```

where `D_W(L)` is the intrinsic compression-centralizer defect. The
radical is infinite, locally finite, perfect and residually finite.

**Why it is worth recording separately.** This is the first group in the
graph whose MF radical is an infinite locally finite group. It is
therefore a confirming instance of
`locally-finite-defect-subgroup-dies-in-every-corona` with `A` infinite,
locally finite, noncentral and equal to the whole defect — and not a
proof of it, since the criterion consumes a commuting-conjugate relation
that normality plus containment in the defect does not supply. The
instance gets that relation from disjointness of lamp supports.

**What is not new.** The non-MF half alone was already reachable from
`finite-dimensional-kazhdan-fixed-algebra-transport`: the `L`-orbit of
`uL` has size `[L:uLu^-1]=8`, so the lamps over that orbit form a finite
subgroup normalized by `L`, its C*-algebra is a finite-dimensional
invariant subalgebra, and fixed-algebra transport identifies the orbit
copies and abelianizes the image. Section 4 of the recheck artifact
gives that derivation in full. The gains of the criterion route are that
it needs no finite index, no invariant algebra and no wreath structure,
and that it exhibits a locally finite radical where the finite-block
construction cannot.

DERIVATION
affine-perfect-lamp-wreath-radical-proof
