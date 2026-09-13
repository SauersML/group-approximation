---
rg: 2
id: twisted-rope-trick-container-is-not-fp3-over-fp2-hosts
kind: claim
title: "The twisted rope-trick container is never FP_3(Q) when the host of the double has finite rational H_2"
invalidates:
  - f3-hosts-for-fp-groups-via-rope-trick-over-fp2-host
distinct_from:
  higman-rope-trick-group-is-never-fp3: that is the untwisted case with one embedding over an arbitrary finitely generated host, read from the source; this allows two different embeddings of the double and needs the host to have finite-dimensional rational H_2 unless the embeddings agree on H_2
  fp2-vertex-graph-of-groups-infinite-h2-edge-kills-fp3: that concerns arbitrary finite graphs of groups whose vertex groups have finite rational H_2; here the vertex group P x G may have infinite rational H_2 because G may
---

Keep the notation of `twisted-rope-trick-embeds-g-in-a-finitely-presented-group`:
`G = F/R` with `F` free of finite rank, `L = F_1 *_R F_2`, `π: L → G`, and
`ι, ι': L → P` injective into a finitely generated group `P`. Suppose `G` is
infinite and `R ≠ 1`, so `R` has infinite rank. Let
`V = ker(H_2(ι; Q) − H_2(ι'; Q)) ∩ ker H_2(π; Q) ≤ H_2(L; Q)`.

If `V` is infinite-dimensional, then `H_3(Hig_{ι,ι'}(G); Q)` is
infinite-dimensional, so `Hig_{ι,ι'}(G)` is not of type `FP_3(Q)`. This
happens in particular:

1. when `H_2(ι; Q) = H_2(ι'; Q)`, for instance `ι' = ι` or `ι'` a conjugate
   of `ι` by an element of `P`. This includes Theorem B of Fournier-Facio–
   Zaremsky, arXiv:2607.21727v1;
2. when `dim_Q H_2(P; Q) < ∞`, for instance `P` of type `FP_2(Q)`, whatever
   `ι` and `ι'` are.

This kills the route `f3-hosts-for-fp-groups-via-rope-trick-over-fp2-host`.

**What is left for a higher rope trick.** A rope-trick container of this
shape can be of type `FP_3(Q)` only if `H_2(ι) − H_2(ι')` is injective on
`ker H_2(π; Q)` up to a finite-dimensional subspace. Here `ker H_2(π; Q)` is
the infinite-dimensional space `([F, R]/[R, R]) ⊗ Q` (Lemma 3.4 of the source).
So `H_2(P; Q)` must be infinite-dimensional, and the two embeddings must differ
there in an essentially injective way. For the container to have finite
rational `H_2`, the difference must also be almost onto the part of
`H_2(P; Q)` that the embeddings do not cancel. The open claim
`acyclic-host-twisted-rope-container-is-of-type-fp3` names a container that
meets both conditions.
