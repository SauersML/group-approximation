---
rg: 2
id: decidable-algebras-embed-in-z2-sft-boundary-product-hosts
kind: claim
title: Every decidable group algebra over F_2 embeds unitally in B_Ω ⊗ L_∂ for some free minimal Z^2-SFT Ω with finitely presented crossed product
distinct_from:
  decidable-group-algebras-have-fp-cantor-crossed-hosts: that allows any torsion-free Farrell–Jones acting group and any Cantor space; this fixes the acting group Z^2 × F_d and the space Ω × ∂F_d with Ω a free minimal Z^2-SFT, and implies that claim.
  free-minimal-z2-sft-is-quantum-rigid: that asks for one quantum rigid free minimal Z^2-SFT over some field; this asks, over F_2, for a family of them whose boundary tensors contain every decidable group algebra.
artifacts:
  - research/artifacts/cantor-crossed-host-boundary-products-2026-09-17.md
---

**OPEN.** Let `G` be a finitely generated group with solvable word problem.
Then there are:
- a free minimal `Z^2`-SFT `Ω` over `F_2` with `B_Ω = LC(Ω, F_2) ⋊ Z^2` finitely
  presented;
- some `d >= 2`;
- a unital embedding `F_2[G] -> B_Ω ⊗ (LC(∂F_d, F_2) ⋊ F_d)`.

**Why it matters.** Through
`cantor-crossed-hosts-are-closed-under-boundary-products`, it implies
`decidable-group-algebras-have-fp-cantor-crossed-hosts` (route
`cantor-crossed-hosts-via-boundary-products-of-z2-sft-hosts`), and hence
`boone-higman-conjecture` along the graph's chain.

Unlike the bare `Z^2` case (Attempt 2 on the target), a positive answer does
not make `G` linear sofic through a rank model, because the host has none.

**Prerequisites that can fail separately** (artifact Section 4):
- (Q) Existence of one quantum rigid free minimal `Z^2`-SFT over `F_2`. This is the
  `F_2` form of `free-minimal-z2-sft-is-quantum-rigid`.
- (H) The SFTs used must have no uniform recursive language bound. That this is
  necessary is only sketched: it is the table argument of Attempt 6 on the
  target, run over `Z^2 × F_d`.
  - Without freeness and rigidity, hard minimal SFTs exist
    (`minimal-z2-sfts-have-no-uniform-language-time-bound`).
- (E) The embedding.

## Attempts

- **Kazhdan need d2d6a0cb: Schreier-level invariants of (T) that cannot kill it (2026-09-18,
  swarm-0917-w11-w11-z-pull; unreviewed).** Question: does an infinite Kazhdan group have an infinite
  transitive orbit with an injective bounded-left-displacement map into `Z^2 × F_d`? The sibling
  lease (w11-z-break) reduced the NO answer to the OPEN
  `kazhdan-schreier-graphs-have-superquadratic-ball-separation`. The items below record which
  consequences of (T) survive passage to a single orbit, and why each of them fails over `T × Z^2`.
  1. *Energy rigidity holds, but it is not enough.* Let `F` be a function on the orbit with
     `F∘s − F ∈ ℓ²` for every generator `s`. Then `s ↦ F∘s − F` is a 1-cocycle for the permutation
     representation on `ℓ²(orbit)`. By (T) it is a coboundary, so `F` is a constant plus an `ℓ²`
     function. However `Cay(Z^2 × F_d) = T × Z^2` has the same property, since its first `ℓ²`-Betti
     number vanishes and the group is nonamenable. So no finite-energy test function separates the
     two. Pulled-back tree walls are not commensurated here: their coboundaries lie in `p⁻¹(edge)`,
     which injects into `B_T(L) × Z^2` and may be infinite.
  2. *Weighted walls fail.* Try `F = 1_(A_e) · h(q(x)) · w(p(x))`, with `h` defined on `Z^2` and `w`
     on the tree. When `w` does not decay, the energy diverges on the infinite `Z^2`-fibres inside
     `A_e`. When `w` decays fast enough for `F`'s energy to be finite, `F` is already in `ℓ²` and the
     cocycle is trivially a coboundary.
  3. *The Koopman and measure routes are dead.*
     - If `K` preserves a probability measure on `Ω × ∂F_d`, then its orbit relation is a
       measure-preserving subrelation of an amenable relation. So `K` has a.e. finite orbits
       (Connes–Weiss), and `dense-finite-free-orbits-force-finite-kazhdan-subgroups` applies.
     - No such measure exists in general. The Koopman representation on `L²(μ⊗ν)` is tempered in the
       `F_d`-direction, so it does not almost contain the trivial representation, and (T) gives
       nothing.
  4. *Groupoid amenability is harmless.* `Z^2 × F_d` acts topologically amenably on `Ω × ∂F_d`. So
     the germ groupoid of `K`, an open subgroupoid, is amenable. Orbits through free points therefore
     have property A uniformly. Exact Kazhdan groups (`SL_3(Z)`, `SL_3(Z[1/p])` on its `p`-adic flag
     variety) have this property on free orbits as well, so it gives no contradiction.
  5. *Natural test orbits pass the separation test, heuristically only.* Take `SL_3(Z)` on primitive
     vectors, whose stabilizer is `Z^2 ⋊ SL_2(Z)`. By Lubotzky–Mozes–Raghunathan the Schreier graph is
     quasi-isometric to `H \ X` for the thick orbit.
     - In Iwasawa coordinates `(λ, u, m)`, the fibre over `(λ, m)` is the flat torus `R²/Z²m` scaled by
       `λ^(−3/2)`. This gives a flaring end, and balanced separators of `D`-balls are exponential
       in `D`.
     - `SL_3(Z[1/p]) / SL_3(Z)` is the vertex set of the `Ã₂` building. There, panel trees force
       exponential separators.
     - So neither orbit is a counterexample to the superquadratic conjecture, and neither answers the
       need positively. Neither estimate is written out.
  6. *Stuck at:* a (T)-specific statement stronger than "FW relative to finite-boundary sets". It must
     control walls whose coboundary has quadratic growth. Items 1–4 show that (T) acting on
     `ℓ²(orbit)`, invariant measures and the amenable germ groupoid do not supply it.
