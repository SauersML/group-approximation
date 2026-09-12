---
rg: 2
id: genus-three-mcg-has-no-covering-lift-to-marked-covers
kind: claim
title: No finite-index subgroup of the genus-three closed-surface mapping class group lifts to a marked mapping class group of a finite cover
distinct_from:
  closed-mcgs-have-no-covering-lift-to-marked-covers: that is the same no-go for genus at least four, from Chen--Salter's Theorem A; this is genus three, from the genus-three non-splitting.
  birman-sequence-genus-three-does-not-virtually-split: that is the non-splitting of the genus-three point-pushing extension; this says that no finite cover with marked points, and no lift of any kind, gets around it.
artifacts:
  - research/artifacts/bh-birman-genus3-section-2026-09-12.md
---

**ESTABLISHED (depends on the unreviewed genus-three non-splitting).** Let `Σ` be a
closed orientable surface of genus 3. None of the following exist together:
- a finite-index subgroup `L ≤ Mod(Σ)`;
- a finite unbranched covering `π: Σ̃ → Σ`;
- a finite nonempty `P ⊂ Σ̃`;
- a homomorphism `λ: L → Mod(Σ̃, P)` such that every `λ(f)` has a representative
  covering a representative of `f`.

`λ` is not required to be injective.

**Why it matters.** This is the genus-three case of the BFFHZ one-puncture step
(arXiv:2503.21882v2, Section 4), transplanted to a closed surface. That step would
lift to a finite cover with marked points and then land in a punctured mapping class
group that satisfies PBH. Together with `closed-mcgs-have-no-covering-lift-to-marked-covers`,
the covering template for `closed-surface-mapping-class-groups-satisfy-boone-higman`
now fails in every genus `g ≥ 3`.

**Scope.** Unbranched covers only. Non-covering embeddings into punctured mapping
class groups are not excluded (`closed-mcgs-virtually-embed-in-punctured-mcgs`).

The derivation is `genus-three-covering-lift-no-go-proof`.
