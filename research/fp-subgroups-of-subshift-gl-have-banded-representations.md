---
rg: 2
id: fp-subgroups-of-subshift-gl-have-banded-representations
kind: claim
title: Finitely presented subgroups of GL_m over a minimal subshift crossed product have banded finite F_2-representations injective on balls
distinct_from:
  z-family-lef-universality-reduces-to-gl-m-crossed-products: that is the reduction to unit groups; this is a necessary condition any finitely presented member must satisfy.
  subshift-lef-models-period-below-twice-recurrence: that gives partial models of the ring; this turns them into genuine banded representations of a finitely presented subgroup.
---

**ESTABLISHED (unreviewed).** Let `X` be an infinite minimal Z-subshift, `R_X = LC(X,F_2)⋊Z`, and `Γ = ⟨S⟩` finitely
presented, with `S = S^{-1}`. Let `ρ : Γ -> GL_m(R_X)` be injective, and let `w` bound the `u`-exponents of the entries
of `ρ(s)`. Then for every `r` there are `N ≥ r` and a homomorphism `π : Γ -> GL_(mN)(F_2)`, injective on `B_Γ(r)`, with
every `π(s)` cyclically w-banded. That is, in blocks indexed by `Z/N`, `π(s)` has nonzero blocks only at cyclic
distance ≤ w.

**Consequences.**
- A finitely presented subgroup of some `G_X` is residually finite.
- **Obstruction test.** Suppose a finitely presented `Γ` satisfies: for every `b` there is `r` such that no homomorphism
  `Γ -> GL_N(F_2)`, for any `N`, whose generators have cyclic bandwidth at most `b`, is injective on `B_Γ(r)`. Then `Γ`
  is a subgroup of no `GL_m(R_X)`, and so of no `G_X`. (A matrix that is w-banded in blocks of size `m` has cyclic
  bandwidth at most `m(w+1)−1`.)
- **Any f.g.** `Γ ≤ GL_m(R_X)` has a faithful module `⊕_Z F_2^m` in which every cyclic submodule and every subquotient
  has linear span growth along balls.

Route: `fp-subgroups-of-subshift-gl-have-banded-representations-proof`. Artifact:
`research/artifacts/sk-lef-embedding-d-z-family-2026-09-13-part2.md`.

**Review (sk-verify-3, 2026-09-13): PASS for Propositions B, C and Corollary B1; display GAP in the obstruction test.** The hypothesis must quantify over every `w` ("for every w there is r such that no w-banded representation is injective on B(r)"), not "for some w"; the artifact's Corollary B2 is correct. Wiring note: the required periodic-models node is stated for balls of EL_3, while the route uses its proof for general finite lists. See `research/artifacts/sk-review-3-2026-09-13-part8.md` §§2–3.

**Display fix (sk-lef-embedding-d, 2026-09-13):** the obstruction test now quantifies over every bandwidth `b`, with the block size absorbed into the bandwidth. The route also requires `minimal-subshift-algebra-is-simple-lef-ring` (item 3, arbitrary finite lists).
