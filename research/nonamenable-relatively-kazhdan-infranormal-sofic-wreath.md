---
rg: 2
id: nonamenable-relatively-kazhdan-infranormal-sofic-wreath
kind: claim
title: A coset wreath over a non-amenable, relatively Kazhdan, infranormal subgroup containing SL2(Z) is sofic and carries a compression defect
artifacts:
  - research/artifacts/free-nonsofic-action-sources-verified-2026-09-11.md
distinct_from:
  relatively-kazhdan-amenable-pairs-allow-sofic-defects: that compresses the amenable subgroup Z^2 and gets soficity from amenable point stabilizers; this compresses Z^2 x| SL2(Z), whose stabilizers are non-amenable, and gets soficity from an amenable normal subgroup acting transitively.
  arithmetic-coset-wreath-is-not-sofic: that is the open nonsoficity of an arithmetic wreath whose integral stabilizer is incompressible and co-dense; this is a sofic wreath whose stabilizer is compressible and not co-dense, and it calibrates which hypothesis a proof must use.
---

**ESTABLISHED** (proof in `nonamenable-relatively-kazhdan-infranormal-sofic-wreath-proof`).

Let `D = Z[1/2]` and put

```text
Lambda = SL_2(Z) x <2I> <= GL_2(D),     G = D^2 x| Lambda,
Gamma  = Z^2 x| SL_2(Z) <= G,           t = 2I,
X = G/Gamma,     H = (direct_sum_X Z/2) x| G.                            (NRK1)
```

1. `Gamma` is non-amenable, `(Gamma, Z^2)` has relative property (T), and `Gamma` is
   infranormal but not normal in `G`, with compressor `t`: `t Gamma t^-1 = (2Z)^2 x| SL_2(Z)`.
2. `H` is sofic.
3. `H` has a nontrivial compression defect over the pair. `z = e_Gamma` centralizes `Gamma`,
   but `[t z t^-1, (e_1, I)] != 1`. So `G` does not normalize `C_H(Gamma)`.
4. Consequently (`binary-free-and-ordinary-coset-wreaths-share-hyperlinearity`, items 1 and 5)
   the centralizer HNN group `G *_Gamma (Gamma x Z)` is hyperlinear. Its stable letter is a
   subgroup-central unitary that is not central for `G`.

## Calibration for family D at n = 2

`(G, Gamma)` has every n = 2 ingredient of the dyadic pair `SL_2(Z) < SL_2(Z[1/2])`:
- a non-amenable virtually free integral `SL_2`;
- commensuration of `Gamma`;
- a relatively Kazhdan lattice core (`Z^2`, in the affine form).

It adds an infranormal compressor, which Kun–Thom Theorem A needs and which the arithmetic
pair lacks (`arithmetic-integral-subgroup-is-incompressible`). Yet the wreath is sofic.

What `(G, Gamma)` lacks is **co-density**:
- `G` maps onto `Z` (`t -> 1`) with `Gamma` in the kernel;
- the amenable normal subgroup `B = D^2 x| <2I>` acts transitively on `X` with amenable
  stabilizer `Z^2`, and the soficity proof runs entirely through `B`.

For `A = SL_2(Z[1/2])` the amenable Borel subgroup also acts transitively on `A/SL_2(Z)` with
amenable stabilizer, but it is not normal. Every normal subgroup of `A` is central or of finite
index (background, not part of this claim).

**Reading.** A proof that the dyadic coset wreath is nonsofic, or that `G_2` is nonhyperlinear,
cannot rest only on non-amenable virtually free stabilizers, relative (T) or compression. It
has to use co-density or normal-subgroup rigidity of the arithmetic actor. This is the
brief's "(T)-free setting" test: relative (T) plus infranormality, without (T) of both groups
and without co-density, does not obstruct.
