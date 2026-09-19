---
rg: 2
id: jacobson-haar-lattice-duals-are-class-bijective-extensions
kind: claim
title: Every lattice dual of the Jacobson Haar relation inside its S-arithmetic envelope is a class-bijective extension of that relation, so duality transfers approximations to EL_n(J) but cannot supply them
distinct_from:
  jacobson-haar-relation-is-laurent-affine-restriction: that identifies R_E with the restricted affine relation R_Γ|_D of one discrete group; this places Γ as a lattice in the S-arithmetic envelope G = G_∞ x G_0, computes every lattice dual Δ ↷ Γ\G, and shows each is a class-bijective extension of R_Γ|_D.
  jacobson-haar-relation-is-kazhdan-and-unsplittable: that kills treeings and ergodic amalgam gluings of the two halves; this kills the lattice-duality route recorded as the Next step of binary-jacobson-el3-is-sofic, by a factor-map invariant, not by rigidity.
  paunescu-class-is-measure-equivalence-invariant: that transfers soficity of all actions along measure-equivalence couplings; this studies one coupling where Δ is a lattice of the point stabilizer H, not of G, so the output is an extension and not an SOE.
artifacts:
  - research/jacobson-haar-relation-lattice-duals-proof.md
---

**ESTABLISHED** (route `jacobson-haar-relation-lattice-duals-proof`, swarm-0917-w15-w15-nh-last1, 2026-09-19,
unreviewed). This is a class-kill with a transfer theorem. The target `binary-jacobson-el3-is-sofic` stays **OPEN**.

**Setup.** The notation `n >= 3`, `A = F_2[x, x^(-1)]`, `Γ = A^n x| SL_n(A)` (`SL_n(A) = EL_n(A)`, since `A` is
Euclidean), `D` and `R_Γ|_D` is that of `jacobson-haar-relation-is-laurent-affine-restriction`.
* The two places of `F_2(x)` outside `Spec A` give `K_∞ = F_2((x^(-1)))` and `K_0 = F_2((x))`, with rings
  `O_∞ = F_2[[x^(-1)]]` and `O_0 = F_2[[x]]`.
* `G_v = K_v^n x| SL_n(K_v)` and `G = G_∞ x G_0`. `Γ` embeds diagonally.
* `H = SL_n(K_∞) x G_0` is the stabilizer of `0` for the action of `G` on `K_∞^n` through `G_∞`.

**Theorem.**
1. **(D1, envelope.)**
   * `Γ` is a lattice in `G`, and `G/H = K_∞^n` Γ-equivariantly, with the affine action.
   * `H ↷ (Γ\G, Haar)` is essentially free and ergodic.
   * `H` has lattices, for example `Δ_std = SL_n(F_2[x]) x (F_2[x^(-1)]^n x| SL_n(F_2[x^(-1)]))`.
2. **(D2, transfer.)** Let `Δ` be any lattice of `H`.
   * If `Δ ↷ (Γ\G, Haar)` is sofic, then `EL_n(J)` is sofic.
   * If `L^∞(Γ\G) x| Δ` is Connes-embeddable, then `EL_n(J)` is hyperlinear.
3. **(D3, class-kill.)** For every lattice `Δ` of `H`, the relation `R_Δ` on `Γ\G` is stably orbit equivalent to the
   skew product `S_Δ` of `R_Γ|_D` by the non-atomic probability `H`-space `H/Δ`.
   * The projection `S_Δ -> R_Γ|_D` is a **class-bijective factor map**. Such maps carry soficity and CE only
     downward: from `S_Δ` to `R_Γ|_D`.
   * The fibre-free alternative has no lattice to dualize to. It uses the lcsc group `H' = K_0^n x| SL_n(A)`, with
     `SL_n(A)` discrete, acting on the compact solenoid `Y = (K_∞ x K_0)^n / A^n`. Its cross-section relation on
     `D` is exactly `R_Γ|_D`, a tautology.
   * `Γ ↷ Y` has no finite orbits, because the translation subgroup `A^n` embeds in `Y`. So the periodic-point
     schemes of the two halves do not extend to it.

**What this kills.** Lattice duality with `Γ\(G_∞ x G_0)` was the proposed next step of `binary-jacobson-el3-is-sofic`.
It is a reformulation into an equal-or-stronger problem:
* the invariant is the class-bijective factor map `S_Δ -> R_Γ|_D`;
* every member dies at the step "approximate `S_Δ`", which already contains an approximation of `R_Γ|_D`, since
  `[[R_Γ|_D]]` embeds trace-preservingly in `[[S_Δ]]`.

A duality argument can help only if it brings **extra structure of `S_Δ` that is not visible on `R_Γ|_D`**. The sources
of such structure are the fibre `H/Δ` and the product decomposition `Δ = Δ_∞ x Δ_0`. That is the precise surviving
sub-question:

**(D4, open).** Is `Δ_std ↷ Γ\G` sofic, for example by combining the product structure `Δ_∞ x Δ_0` with the congruence
tower of `Γ`?

Both factors of `Δ_std` are Kazhdan for `n >= 3`. So the approach must avoid the same gluing obstruction as the halves
of `R_Γ|_D`.

Proof: [[jacobson-haar-relation-lattice-duals-proof]].
