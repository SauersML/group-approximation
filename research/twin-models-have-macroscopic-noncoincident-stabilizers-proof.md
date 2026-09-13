---
rg: 2
id: twin-models-have-macroscopic-noncoincident-stabilizers-proof
kind: route
title: Selberg (tau) makes almost invariant vectors radial around both adjacent vertices, which the tree forbids; stabilizer laws then push to a Reiter-almost-invariant measure on vertices
target: twin-models-have-macroscopic-noncoincident-stabilizers
requires:
  - sl2-z-inverse-p-over-sl2-z-is-codense-tau-pair
  - expanding-matchings-need-a-shared-stabilizer
artifacts:
  - research/artifacts/dyadic-twin-noncoincidence-2026-09-13.md
---

Full proof in the artifact, Sections 1–4.

* **Lemma 1.** A finite-index subgroup of a vertex group has a finite nonempty fixed subtree. An
  infinite one would contain a fixed ray, which would put a finite-index subgroup of `PSL_2(Z)`
  inside a Borel subgroup. So the tree center `z(H)` is defined, and it is conjugation-equivariant.
* **Item 1.** `(τ)` for `C_0` on the congruence spheres around `v_0`, and for `C_1` on those around
  `v_1`, forces an almost invariant vector to be close to radial around both vertices. For a vector
  `f_0` radial around `v_0` with sphere values `a_j`, the projection onto `v_1`-radial vectors gives
  `||f_0 − P_(K_1)f_0||^2 = (2/3)Σ_j 4^j(a_j − a_(j+1))^2 >= (1/9)||f_0||^2`. Substitute
  `x_j = 2^j a_j` and use `||x − Sx/2|| >= ||x||/2`.
* **Item 2.** The stabilizer laws `μ_i` are exactly `C_i`-conjugation invariant. The coupling gives
  `TV(μ_0, μ_1) <= 1 − p`. Push `μ_0` to type-0 vertices through the center kernel. The result is
  `4(1 − p)`-almost invariant in `ℓ^1` under `S_0 ∪ S_1`. Powers–Størmer and item 1 give
  `λ_A^2 <= 4(1 − p)`.
* **Item 3.** At points deep on both sides, coincidence of the `C_i`-stabilizers equals coincidence
  of the `Δ_R`-stabilizers. Lemma G of `expanding-matchings-need-a-shared-stabilizer`, applied to the
  identity bijection orbit by orbit against total defect `|S_Δ|ε|W|`, charges `h|H ∩ O|` to every
  non-coincident diagonal orbit with Cheeger constant at least `h`. ∎
