---
rg: 2
id: closed-mcgs-have-no-covering-lift-to-marked-covers
kind: claim
title: For genus at least four no finite-index subgroup of a closed-surface mapping class group lifts to a marked mapping class group of a finite cover
invalidates:
  - closed-mcg-bh-via-covering-lift-to-marked-cover
distinct_from:
  outer-covering-lifts-are-virtual-sections: that is the general equivalence between covering lifts and virtual sections, valid in every genus and for free groups; this is its consequence for closed surfaces of genus at least four, where Chen--Salter rule virtual sections out.
  birman-exact-sequence-does-not-virtually-split: that is the non-splitting of the point-pushing extension; this says that no finite cover with marked points, and no lift of any kind, injective or not, gets around it.
artifacts:
  - research/artifacts/bh-out-fn-closed-mcg-2026-09-12.md
---

**ESTABLISHED.** Let `Σ` be a closed orientable surface of genus `g ≥ 4`. None
of the following exist together:
- a finite-index subgroup `L ≤ Mod(Σ)`;
- a finite unbranched covering `π: Σ̃ → Σ`;
- a finite nonempty `P ⊂ Σ̃`;
- a homomorphism `λ: L → Mod(Σ̃, P)` such that every `λ(f)` has a
  representative covering a representative of `f`.

`λ` is not required to be injective.

**Why it matters.** The one-puncture step of BFFHZ, arXiv:2503.21882v2
Section 4, is such a lift for a once-punctured surface: the lift fixing both
punctures of the double cover. Transplanting that template to a closed surface
of genus at least four would mean: pass to a finite cover, choose lifts that fix
marked points, and land in a punctured mapping class group that already
satisfies PBH. That cannot be done for any cover. This kills the route
`closed-mcg-bh-via-covering-lift-to-marked-cover`.

**Scope.**
- **Unbranched covers only.** A branched cover needs representatives preserving
  the branch set, and that variant was not analysed.
- **Genus 3 is not covered.** There the construction is equivalent to a virtual
  section of the genus-3 Birman sequence (`outer-covering-lifts-are-virtual-sections`),
  and Chen--Salter's Theorem A starts at genus four.
- **Non-covering embeddings** of finite-index subgroups into punctured mapping
  class groups are not excluded. That is the open premise
  `closed-mcgs-virtually-embed-in-punctured-mcgs`.

The derivation is `closed-mcg-covering-lift-no-go-proof`.
