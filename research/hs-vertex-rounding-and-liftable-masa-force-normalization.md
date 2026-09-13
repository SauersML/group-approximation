---
rg: 2
id: hs-vertex-rounding-and-liftable-masa-force-normalization
kind: claim
title: Vertex rounding plus one liftable masa of the actor commutant forces normalization, with no per-block gap
distinct_from:
  hs-rounding-and-actor-gap-force-ccr: that assumes the per-block homogeneous Poincare gap (H2')(b) and runs the median step block by block; this assumes only that the actor commutant has a liftable masa and replaces the median step by maximality of the masa, so the per-block gap is never used.
  hs-block-gap-iff-liftable-masa-of-actor-commutant: that proves a liftable masa is equivalent to the summed gap (F2) and supplies the center clause; this consumes the masa directly to concentrate the median observable and concludes normalization.
artifacts:
  - research/artifacts/hs-s4-assembly-2026-09-12.md
  - research/artifacts/unified-compression-rigidity-2026-09-12.md
---

**ESTABLISHED.** Let `Gamma < G` be an infranormal pair of Kazhdan groups, `(F, kappa)` a
Kazhdan pair for `Gamma`, and `t_1, ..., t_k` strict compressors with
`G = <Gamma, t_1, ..., t_k>`. Let `sigma : G -> U(M)`, `M = prod_U M_n`, be trace-preserving
with coordinates `sigma_n`, and put `Q = sigma(G)' cap M`. Assume:

- **(H1)** of `hs-stable-vertex-rounding-for-every-model` for `sigma`: after `o(n)` padding
  there are genuine `pi_n : Gamma -> U(n')`, `n'/n -> 1`, with
  `max_(s in F) ||sigma_n(s) - pi_n(s)||_2 -> 0`;
- **(LM)** `Q` has a maximal abelian subalgebra of the form `C = prod_U C_n`, where `C_n` is
  spanned by a finite partition of unity `{q_(n,A)}` of `M_n` by projections.

Then `sigma(t_i Gamma t_i^(-1))' cap M = sigma(Gamma)' cap M` for each `i`, and `sigma(G)`
normalizes `sigma(Gamma)' cap M`.

## What changes

`hs-rounding-and-actor-gap-force-ccr` needs (H2'): boundary (a), a homogeneous Poincare gap on
every block (b), and a center clause (c).
- (a) and (c) follow from (LM) and (H1) (`hs-block-gap-iff-liftable-masa-of-actor-commutant`,
  items 1 and 5).
- (b) is not needed. Its only use was to pin the block median observable at `1/2`. Maximality of
  the masa does this: the observable lies in `Q` and commutes with the blocks, so it is a function
  of the blocks, and a median bound finishes.

So the open actor input of the Hilbert--Schmidt median route is exactly (LM),
[[actor-commutant-has-liftable-masa-in-every-model]]. This answers the item recorded on
`hs-coarse-actor-gap-at-compressor-generators`: the median step runs on the bounded (masa) form
of the gap.

In the language of `research/artifacts/unified-compression-rigidity-2026-09-12.md`, (H1) is the
rounding face (R) and (LM) the localization face (L) of property (T) in the Hilbert--Schmidt
row. (LM) is the Hilbert--Schmidt form of Kun--Thom Lemma 2.3 applied to `G`.

Derivation: `hs-vertex-rounding-and-liftable-masa-force-normalization-proof`.
