---
rg: 2
id: peirce-root-preserving-subshift-el3-isos-force-orbit-equivalence
kind: claim
title: An isomorphism G_X → G_Y carrying the six root subgroups onto the Peirce root groups of some decomposition of I into three nonzero idempotents is standard, and then X and Y are strongly orbit equivalent
artifacts:
  - research/artifacts/sk-iso-rigidity-2026-09-13-part1.md
distinct_from:
  root-preserving-subshift-el3-isos-force-orbit-equivalence: that assumes the standard root subgroups of G_Y; this allows the Peirce root groups of any decomposition of I, which is exactly the class of standard isomorphisms
  subshift-elementary-group-isomorphism-forces-orbit-equivalence: that open claim concerns arbitrary isomorphisms; this reduces it to recognizing the images of root subgroups as Peirce root groups
---

Let `X, Y` be infinite minimal subshifts, `R_X = LC(X,F_2) ⋊ Z`, `G_X = EL_3(R_X)`, and `M = M_3(R_Y)`. Let
`α: G_X → G_Y` be a group isomorphism. Suppose there are orthogonal nonzero idempotents `E_1, E_2, E_3 ∈ M` with
`E_1 + E_2 + E_3 = I` such that `α` maps the set of six root subgroups `A_ij(R_X)` onto the set of six Peirce root
groups `P_ij = I + E_i M E_j`.

Then there is a ring isomorphism `Θ: M_3(R_X) → M_3(R_Y)` such that either:
- `α = Θ|_{G_X}`; or
- `α(g) = Θ(τ(g)^t)^{-1}` for all `g`. Here `τ(Σ f_j u^j) = Σ u^{-j} f_j` is the canonical anti-automorphism of `R_X`,
  applied entrywise.

In both cases `M_3(R_X) ≅ M_3(R_Y)`, so `X` and `Y` are strongly orbit equivalent.

Conversely, every standard isomorphism satisfies the hypothesis. So "every isomorphism `G_X ≅ G_Y` is standard" is
equivalent to "every isomorphism carries root subgroups onto Peirce root groups".

Status: proved in `peirce-root-preserving-subshift-el3-isos-soe-proof`, unreviewed.

**Review (sk-verify-15, 2026-09-13): PASS.** Fullness from simplicity of M_3(R_Y), the Peirce commuting hexagon (all non-commuting cases), Aut(C_6) = S_3 × reversal, the graph automorphism γ, Theorem P and the PASSed SOE import with m = 3 re-derived. See `research/artifacts/sk-verify-15-2026-09-13-part1.md` §3.
