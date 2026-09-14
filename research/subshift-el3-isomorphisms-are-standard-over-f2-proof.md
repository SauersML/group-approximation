---
rg: 2
id: subshift-el3-isomorphisms-are-standard-over-f2-proof
kind: route
title: Theorem D - Frobenius bicommutants give the Singer identities and no fixed vectors, and Theorem A turns them into a ring isomorphism R_X → R_Y
target: subshift-el3-isomorphisms-are-standard-over-f2
requires:
  - frobenius-bicommutants-make-subshift-el3-isos-standard
artifacts:
  - research/artifacts/sk-orthogonality-o-2026-09-14-part2.md
  - research/artifacts/sk-verify-25a-2026-09-14.md
  - research/artifacts/sk-verify-25b-2026-09-14.md
---

Let `α: G_X → G_Y` be an isomorphism of the groups of two infinite minimal subshifts.

1. By item 5 of `frobenius-bicommutants-make-subshift-el3-isos-standard` (Theorem D), after composing with the graph
   automorphism `γ_X` when the orientation of the constant Frobenius images is `3*`, `α` satisfies the Singer identities
   and (O′).
2. By `singer-identities-make-subshift-el3-isos-standard` (Theorem A, with Fix W3), `α = inn(k)∘M_3(φ)|_{G_X}` for some
   `k ∈ GL_3(R_Y)` and a ring isomorphism `φ: R_X → R_Y`.
3. `M_3(φ)` is a ring isomorphism `M_3(R_X) → M_3(R_Y)`, and composing with `γ_X` corresponds to the anti-isomorphism
   case. So `α` is standard in the sense of the target. ∎

Reviews: sk-verify-25a (line by line) and sk-verify-25b (adversarial, with MSI computations), both PASS-WITH-FIXES and
independent; fixes merged by sk-rigidity-merge (2026-09-14). Every import of the chain is reviewed, and Matui's
Lemma 2.5 was read at source by both reviewers. Part 1 §4 of the artifact (Theorem B, Lemma N, Corollary B′) is
unreviewed and not used: Theorem C supersedes it.
