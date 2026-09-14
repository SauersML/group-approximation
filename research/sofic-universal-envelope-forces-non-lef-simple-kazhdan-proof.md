---
rg: 2
id: sofic-universal-envelope-forces-non-lef-simple-kazhdan-proof
kind: route
title: LEF passes to subgroups, and some finitely presented sofic groups are not LEF
target: sofic-universal-envelope-forces-non-lef-simple-kazhdan
requires:
  - gap-sofic-approximations-are-local-embeddings
---

**1. LEF passes to subgroups.** Let `G` be LEF and `H <= G`. A finite `F ⊆ H` is a finite subset of
`G`, so there is a finite group `K` and an injection `φ : F -> K` with `φ(xy) = φ(x)φ(y)` whenever
`x, y, xy ∈ F`. The same `φ` witnesses the condition for `F` as a subset of `H`.

**2. A finitely generated sofic group that is not LEF.** `BS(2,3) = ⟨a, t | t a^2 t^(-1) = a^3⟩` is
finitely presented, residually solvable and therefore sofic, and it is not residually finite, being
non-Hopfian. A finitely presented LEF group is residually finite (Vershik--Gordon 1997), so
`BS(2,3)` is not LEF. The required claim records the same witness in its model test, where it was
reviewed.

**3. Conclusion.** Assume every finitely generated sofic group embeds in an infinite simple sofic
Kazhdan group, and apply this to `BS(2,3)`, obtaining `BS(2,3) <= G` with `G` infinite, simple,
Kazhdan and sofic. If `G` were LEF then `BS(2,3)` would be LEF by step 1, contradicting step 2. So
`G` is sofic, simple, Kazhdan, infinite and not LEF.

**4. Where this leaves the target.** Any proof of the universal statement must therefore produce
sofic approximations that are not local embeddings. By the required claim, such approximations avoid
linear, affine and projective linear targets over finite fields, and avoid automorphism groups of
finite groups acting on themselves. That is the same barrier recorded for the finitely presented
question, reached here from the embedding side.
