---
rg: 2
id: stw99-lxxvi-closed-compact-stratum-realization-proof
kind: route
title: Strict collar embeddings and increasing source classes realize a closed compact stratum
target: stw99-lxxvi-closed-compact-stratum-realization
requires:
  - stw99-lxxvi-first-factor-soft-cu-isomorphism
  - stw99-lxxvi-all-base-compact-rigidity-k-stability
  - stw99-lxxvi-rr0-relative-strict-positive-embedding
artifacts:
  - research/artifacts/stw99-lxxvi-closed-compact-stratum-realization-2026-09-05.md
---

Lift the canonical soft part sigma([b]) to a source positive c, and
lift the compact bundle on Y to a source projection P_Y. Projection
extension and local polar frames give a neighborhood projection P
with phi[P(x)]<=[b(x)], strictly below the soft target outside Y
where P(x) is nonzero.

On closed collars disjoint from Y, strict relative selection embeds
P into Her(c). Extend each frame inward through the infinite standard
module, retaining its prescribed collar values. Weighted hereditary
sums then give source positives a_n that are the bundle P on nested
closed neighborhoods K_n shrinking to Y, and have the exact class
of c at every point outside K_n.

Successive a_n compare globally: on K_(n+1) an explicit partial
isometry identifies the two projection bundles, while every nonzero
source cutoff has strict comparison off K_(n+1). The same relative
argument gives phi[a_n]<=[b]. For a representing sup_n[a_n], the
restriction to Y remains P_Y and the other fibers agree with b.
An actual compact boundary frame on Y and strict cutoff comparison
off Y prove the reverse global inequality [b]<=phi[a]. This final
step does not infer global comparison merely from equal fiber classes.
