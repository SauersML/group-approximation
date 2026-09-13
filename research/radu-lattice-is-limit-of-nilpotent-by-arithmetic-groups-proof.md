---
rg: 2
id: radu-lattice-is-limit-of-nilpotent-by-arithmetic-groups-proof
kind: route
title: Quotient by the lower central series of the free kernel, pass to the marked limit, and read the screens off primitivity and finite presentation
target: radu-lattice-is-limit-of-nilpotent-by-arithmetic-groups
requires:
  - radu-horizontal-quotient-is-arithmetic-lattice
  - radu-bmw-lattice-embeds-in-titz-witzel-kernel
---

# Proof

**Item 1.**
* `γ_k(Λ_v)` is verbal in `Λ_v`, hence invariant under every automorphism of `Λ_v`. Since
  `Λ_v` is normal in `Γ_R`, conjugation by `Γ_R` preserves `γ_k(Λ_v)`, so it is normal in `Γ_R`.
* Free groups are residually nilpotent (Magnus), so `∩_k γ_k(Λ_v) = 1`. `Λ_v` is free by
  `radu-horizontal-tree-group-is-linear`.
* Fix the finite generating set `S` of `Γ_R`. For a finite ball `B_R` of `Γ_R`, the finitely many
  nontrivial elements `g ∈ B_R` each lie outside `γ_k(Λ_v)` for all large `k`, since the series
  decreases with trivial intersection. So for large `k` the ball of radius `R` in `G_k` with
  respect to `S` equals that of `Γ_R`, and `G_k → Γ_R` as marked groups.
* `Λ_v/γ_k(Λ_v)` is the free nilpotent group of class `k − 1` on a basis of `Λ_v`, which is
  infinite. `Q` is linear by `radu-horizontal-tree-group-is-linear`.

**Item 2.** Suppose `G_k` is sofic for all `k`. Given `R` and `ε`, choose `k` with
`B_R(G_k) = B_R(Γ_R)` and a sofic approximation of `G_k` that is `ε`-multiplicative and
`ε`-free on `B_R(G_k)`. Its values on `S` define an almost action of `Γ_R` with the same
defects on `B_R`. So `Γ_R` is sofic.

**Item 3.** This is the contrapositive of item 2, since `Λ_v/γ_k(Λ_v)` is nilpotent, hence
amenable, and `Q` is residually finite. The open status is the one recorded in
`binary-jacobson-weak-sofic-status-proof`, Section 5, which cites Arzhantseva–Berlai–Finn-Sell–Glebsky
§4.4. Not re-read from the paper.

**Item 4.**
* *Primitivity.* `V` acts simply transitively on the vertices of `T_v`, so `Y = Λ_v\T_v` is the
  Cayley graph of `W = V/Λ_v ≅ PGL_2(Z)` on `x, y, z`. The loop of `(xz)^2` at the base vertex
  visits `1, x, xz, xzx = z`, four distinct elements of `W`, so it is an embedded 4-cycle. A
  spanning tree containing three of its edges makes the fourth a free generator of
  `π_1(Y) = Λ_v`. So `(xz)^2` is primitive, and `(xz)^4` maps to a nonzero element of
  `Λ_v^ab = Λ_v/γ_2(Λ_v)`.
* *Not residually finite.* `(xz)^4` lies in the finite residual of `Γ_R`
  (`radu-bmw-lattice-embeds-in-titz-witzel-kernel`, item 2). Any finite quotient of `G_k` is a
  finite quotient of `Γ_R`, so it kills the image of `(xz)^4`, which is nontrivial in `G_k` for
  `k >= 2`.
* *Not LEF.* A marked limit of LEF groups is LEF. A finitely presented LEF group is residually
  finite, because finite models of large balls contain the relators and are finite quotients.
  `Γ_R` is finitely presented and not residually finite.
* *Split host.* `X̃ = T_h × T_v` is simply connected, and `X_Q = Λ_v\X̃ = T_h × Y` has
  `π_1 = Λ_v`. Define `d(g)` as the class in `C_1(X_Q)/B_1(X_Q)` of the image of any edge path in
  `X̃` from the base vertex to `g·base`. Two such paths differ by a boundary in the simply
  connected square complex `X̃`, so `d` is well defined, and `d(gh) = d(g) + ḡ·d(h)`. So
  `g ↦ (d(g), ḡ)` is a homomorphism `Γ_R → (C_1/B_1) ⋊ Q`. For `n ∈ Λ_v`, `d(n)` is the
  homology class of the loop `n` in `H_1(X_Q) = Z_1/B_1 <= C_1/B_1`, which is `n^ab`. So the
  kernel is `[Λ_v, Λ_v]`, and `G_2` embeds.

∎
