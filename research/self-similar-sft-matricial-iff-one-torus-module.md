---
rg: 2
id: self-similar-sft-matricial-iff-one-torus-module
kind: claim
title: For a free minimal Z^2-SFT with a constant-shape self-similarity, exact matriciality holds iff one scale-3 torus tiling algebra has a nonzero finite-dimensional module
distinct_from:
  torus-quantum-tilings-decide-matriciality-of-sft-rings: that needs torus modules at every scale for every free minimal SFT; this reduces to one torus module at scale 3 when a constant-shape Ω-preserving substitution exists
  labbe-wang-shift-crossed-product-is-exactly-matricial: that is the Labbé instance, which this does not reach because Labbé's morphism is not of constant shape
artifacts:
  - research/artifacts/un-labbe-torus-decider-inflation-2026-09-13.md
---

**ESTABLISHED (unreviewed).** Let `Ω` be a free minimal `Z^2`-SFT, `k` a finite field, and `σ` a substitution of
constant shape `S` with both sides `>= 2` and `σ(Ω) ⊆ Ω`. Then `LC(Ω,k) ⋊ Z^2` embeds unitally in an algebraic
ultraproduct of matrix algebras over fields iff, for some finite-index `Λ ≤ Z^2`, the torus tiling algebra
`𝒯_(3,Λ)(Ω,k)` has a nonzero finite-dimensional module.

**Remarks.**
- For aperiodic `Ω` such a module is necessarily contextual: commutative torus modules give periodic legal points.
- **Does not reach Labbé's shift.** Labbé's morphism has letter-dependent shapes. A recognizable constant-shape
  substitution would give rational eigenvalues, which the golden rotation factor of `Ω_U` does not have (recalled; see
  artifact §5.2).

Route: `self-similar-sft-matricial-iff-one-torus-module-proof` (artifact §4).

**Review (un-verify, 2026-09-13): PASS.** (⇒) is the reviewed torus criterion at a scale `≥ max(r,3)` followed by descent to scale 3; (⇐) iterates inflation (`D_(m+1) ≥ D_m + 1`, unbounded), descends to every scale, and applies the reviewed torus criterion (un-review-measure part 3 §L1). Scale-3 algebras use the global language `L_(B_3)(Ω)`, so no relation depends on `r`. See `research/artifacts/un-review-2026-09-13-part10.md` §3.
