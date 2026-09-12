---
rg: 2
id: sfts-without-finite-orbits-are-not-residually-finite-actions
kind: claim
title: Subshifts inside an SFT with no finite orbit carry no residually finite action and have no periodic approximations
distinct_from:
  periodic-approximable-subshifts-host-no-fp-simple-group: That proves full groups of subshifts with periodic approximations host no finitely presented infinite simple group; this proves that subshifts inside SFTs without finite orbits never have periodic approximations, so that obstruction cannot reach them.
  marked-graph-action-not-residually-finite: That concerns the Kun--Thom coset space and a graph-wreath residual finiteness notion; this is Kerr--Nowak residual finiteness for subshifts of finite type, obstructed by the absence of finite orbits.
artifacts:
  - research/artifacts/fp-simple-amenable-z2-sft-2026-09-12.md
---

**ESTABLISHED.** Let `Lambda` be a finitely generated group, `A` a finite alphabet, and `Y ⊆ A^Lambda` a subshift of finite type with no finite `Lambda`-orbit. Let `X ⊆ Y` be nonempty, closed and invariant.

1. The action `Lambda ~ X` is not residually finite in the sense of Kerr--Nowak, as restated by Xin Ma (arXiv:2209.00580, Definition `defn: residually finite action`, read from source).
2. `X` has no periodic approximations in the sense of `periodic-approximable-subshifts-host-no-fp-simple-group`.
3. For `Lambda = Z^2` the hypothesis says `Y` is aperiodic. For every such `X`, the hypotheses of Ma's Theorem C and of `periodic-approximable-subshifts-host-no-fp-simple-group` item 1 fail, so neither result can decide full groups there.

**Proof sketch.** The full proof is in the artifact, Section 2.
- A finite model `(E, beta)` that is `epsilon_0`-close on the SFT shape `K` gives a configuration `y(lambda) = (beta(lambda) z_0)(e)`.
- The `K`-patterns of `y` are those of points of `X`, so `y` lies in `Y`.
- `y` is invariant under the finite-index stabilizer of `z_0`, so its orbit is finite. That contradicts the hypothesis on `Y`.
- (PA) would itself produce a finite-orbit point of `Y`.

No novelty is claimed. This is an elementary pseudo-orbit argument.
