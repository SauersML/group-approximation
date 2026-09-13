---
rg: 2
id: extensions-of-aperiodic-sfts-are-not-residually-finite-actions
kind: claim
title: Residual finiteness of actions passes to factors, so no extension of a perfect subshift of an SFT without finite orbits is residually finite
distinct_from:
  sfts-without-finite-orbits-are-not-residually-finite-actions: That proves the subshift itself is not residually finite; this passes residual finiteness to factors, so every extension fails too, including extensions that are not subshifts of SFTs.
artifacts:
  - research/artifacts/labbe-lef-2026-09-12.md
---

**ESTABLISHED.** Residual finiteness is meant in the sense of Kerr--Nowak, as restated by Xin Ma (arXiv:2209.00580). For every finite `F ⊆ Lambda` and `epsilon > 0` there are:
- a finite `epsilon`-dense `E ⊆ X`;
- an action `beta` of `Lambda` on `E` with `d(s.z, beta(s) z) < epsilon` for all `z ∈ E` and `s ∈ F`.

1. Let `pi : Y -> X` be a factor map of compact metric `Lambda`-spaces, and suppose `X` has no isolated points. If `Lambda ~ Y` is residually finite, then so is `Lambda ~ X`.
2. Let `Lambda` be finitely generated, and let `X` be a nonempty closed invariant subset, without isolated points, of a `Lambda`-SFT with no finite orbit. Then no extension of `Lambda ~ X` is residually finite.
3. Let `Omega_U` be Labbé's shift, and let `pi : Y -> Omega_U` be any extension.
   - `Y` is free.
   - `[[Omega_U]]`, and so `D([[Omega_U]])`, embeds in `[[Y]]` by `ĝ(y) = sigma^{c_g(pi y)} y`.
   - Ma's Theorem C (arXiv:2209.00580, line 405) applies to no such `Y`.

**Proof.** The proof is `extensions-of-aperiodic-sfts-not-rf-proof`. The artifact, Section 2.4, has the details.
- Item 1 transports a finite model on `Y` to distinct points of `X` near its image.
- Item 2 is item 1 combined with `sfts-without-finite-orbits-are-not-residually-finite-actions`.

Consequence: Ma's route to LEF is closed for `D([[Omega_U]])` through every extension, and not only through `Omega_U` itself.
