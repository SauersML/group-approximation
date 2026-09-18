---
rg: 2
id: free-minimal-cantor-crossed-products-are-central-simple
kind: claim
title: The crossed-product algebra of a minimal topologically free action of any countable group on a compact zero-dimensional space is simple with centre the base field
distinct_from:
  free-minimal-crossed-products-are-simple-with-rank-models: that is the case of free minimal Z^d actions and adds rank models; this is any countable acting group, torsion allowed, and needs only topological freeness.
  binary-el-simple-iff-minimal-topologically-free: that is simplicity of the elementary group EL_n over F_2; this is simplicity and trivial centre of the algebra itself over any field, the input that central-simple-leavitt-tensor-unit-groups-are-simple needs.
---

**ESTABLISHED (unreviewed).** Standard; no novelty is claimed.

Let a countable group `Λ` act minimally and topologically freely on a compact Hausdorff
zero-dimensional `X`. Let `k` be a field and `B = LC(X, k) ⋊ Λ` with `u_g f u_g^(-1) = f ∘ g^(-1)`.
Then `B` is simple and `Z(B) = k`.

**Use.** With a free minimal subshift and `k = F_2`, `B` is central simple. This is the hypothesis of
`central-simple-leavitt-tensor-unit-groups-are-simple` and `leavitt-tensor-hosts-acyclic-steinberg-and-fp`
in route `boone-higman-via-leavitt-units-of-rigid-sft-overgroups`.

DERIVATION
free-minimal-cantor-crossed-products-are-central-simple-proof
