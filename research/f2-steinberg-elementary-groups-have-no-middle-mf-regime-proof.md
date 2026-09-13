---
rg: 2
id: f2-steinberg-elementary-groups-have-no-middle-mf-regime-proof
kind: route
title: Trivial scalar centre over F_2 plus simplicity modulo centre collapses the MF spectrum
target: f2-steinberg-elementary-groups-have-no-middle-mf-regime
requires: [simple-el-group-middle-regime-is-a-central-extension-effect, steinberg-elementary-groups-are-simple-mod-centre]
artifacts:
  - research/artifacts/un-m-converse-simple-spectrum-2026-09-13.md
---

Let `N ≥ 3` and `G = EL_N(R)` with `R = A_(F_2)(𝒢)` as in the target.
- By `steinberg-elementary-groups-are-simple-mod-centre` (un-verify PASS · 171f0f7525), every normal subgroup of `G`
  is central or all of `G`, and `Z(G) ⊆ F_2^× I_N = {I_N}`. So `Z(G) = 1`.
- By `simple-el-group-middle-regime-is-a-central-extension-effect` (b), `G` is MF iff it has a nontrivial homomorphism
  to an MF group, so `G` is either MF or MF-rigid, and `N` is not in the middle regime. As `N ≥ 3` was arbitrary, the
  middle regime of `R` lies in `{2}`.

**(M⇐) reduction.** The open claim asks, for `R` simple and stably finite, whether `EL_N(R)` is MF for every `N ≥ 3`. On
this class, being MF at `N ≥ 3` is the same as not being MF-rigid at `N`. So the claim restricted to the class is exactly:
stable finiteness ⇒ `EL_N(R)` is not MF-rigid for every `N ≥ 3`. `[]`
