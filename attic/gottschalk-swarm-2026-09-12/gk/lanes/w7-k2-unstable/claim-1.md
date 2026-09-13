---
rg: 2
id: leavitt-unit-groups-have-no-unstable-k2-at-rank-three
kind: claim
title: The binary and ternary Leavitt unit groups have no unstable K_2 at rank three, so the K_2 option of the Steinberg firewall residue is empty
distinct_from:
  leavitt-steinberg-map-iso-from-rank-three: that imports Khanh's comparison St_r ≅ GL_r for the binary algebra at every rank r >= 3; this reads the rank-three case for both the binary and the ternary host as a presentation of the unit group itself, and records that no element of K_2(3,R) is available to a relation-only proof.
  prime-field-leavitt-tensor-hosts-fp-and-simple-mod-centre: that is the host theorem for B ⊗ L_p under the hypotheses K_1 = K_2 = 0; this takes B = F_3, discharges the hypotheses by Ara--Brustenga--Cortiñas, and draws the firewall consequence at rank three.
  steinberg-group-is-glued-over-the-permutohedron: that presents St_n(R) as the colimit of its ordered unipotent radicals and localizes corona compatibility to hexagons; this identifies the rank-three hexagon colimit with the unit group for both hosts, so a graph-of-groups model on the hexagon descends to the unit group exactly when it kills the one closing letter.
  graphs-of-locally-finite-groups-carry-regular-rank-models: that is the firewall listing an element of K_2(3,R) as one way a relation-only proof could bite; this shows that option is empty.
artifacts:
  - research/artifacts/leavitt-unstable-k2-steinberg-reduction-2026-09-12.md
---

**OPEN** (candidate proof in `## Attempts`; verification requested from `w4-vf-gate`). Let `p ∈ {2,3}` and
`R = L_(F_p)(1,2)`, and identify `R^x ≅ GL_3(R)` through a three-leaf prefix code.

1. `K_n(R) = 0` for every `n`, and `K_2(3,R) = ker(St_3(R) -> GL_3(R)) = 0`. So `K_2(3,R) -> K_2(R)` is injective.
2. `R^x` is presented by the rank-three Steinberg relations over `R`. Each holds in a root-generated subgroup of order
   at most `p^3`.
3. In the Steinberg residue of `graphs-of-locally-finite-groups-carry-regular-rank-models` (firewall artifact
   Remark 3.2), the option "an element of `K_2(3,R)`" is empty. A relation-only proof has to use a cycle of Steinberg
   relations that no graph of locally finite subgroups routes, or a global input.
4. `R^x ≅ π_1(Y_hex)/<<t>>`. Here `Y_hex` is the hexagon of the six unipotent radicals `U_π(R)`, `π ∈ S_3`, amalgamated
   along adjacent intersections, and `t` is the letter of the one edge off a maximal tree.

**Not claimed.**
- Point 4 is a presentation, not a firewall for the two-root defect. The `U_π` contain no cylinder frames, so the
  graph-of-groups model gives no `D_A` statement on `Y_hex`. A frame vertex `L_0` leaves `R^x *_K L_0` after killing
  `t`.
- The rank-two kernel `ker(St_2(R) -> E_2(R))`.
- A ternary graph-of-groups model on `Y_hex`.

**Payoff.** Of the three ways a relation-only proof of the binary gates could bite, two remain: nonsofic Steinberg
cycles, and global inputs. For the representation form of `binary-complement-corner-has-no-weakly-finite-image`,
point 4 puts the first on one relation. A nontrivial weakly finite model of `π_1(Y_hex)` that kills `t` refutes that
claim. The graph-of-groups model satisfies every relation of `π_1(Y_hex)` and is nontrivial, so a relation-only proof
of that claim has to use `t = 1`.

## Attempts

- 2026-09-12 `w7-k2-unstable`: candidate proof, artifact Sections 1–5. Held OPEN until `w4-vf-gate` re-derives it.
  * **Stable K-theory.** Theorem 7.6 of `abc-leavitt-path-k-theory-exact-sequence` for one vertex with two loops has
    `1 - N^t = -1`, so `K_n(L_k(1,2)) = 0` over every field (`ara-cortinas-leavitt-tensor-k-theory-vanishes`).
  * **Binary.** (KH2) of `leavitt-steinberg-map-iso-from-rank-three` at `r = 3`, re-derived through Khanh's
    Theorem 5.4:
    - the five-term sequence with `H_2(GL_3) = 0` and perfect `St_3` gives `N_3 = [St_3, N_3]`, and Lemma 5.2 gives
      `j_3(N_3) = 1` in `St_4`;
    - Theorem 5.1 gives `N_4 = 1`;
    - the refinement is `D_3 = F_α ∘ St(α_3)` for the coarse family `(E_11, E_22, E_33 + E_44)`, which is `α_3` of the
      standard family. It is bijective by Voronetsky, Proposition 1 at `n = 4` with `S = {1}`, read from
      arXiv:2004.08551v2 (p. 9: "a surjection for n ≥ 3 and a bijection for n ≥ 4");
    - `φ_4 D_3 = α_3 φ_3` gives `N_3 = D_3^(-1)(N_4) = 1`.
  * **Ternary.** Part 2 of `prime-field-leavitt-tensor-hosts-fp-and-simple-mod-centre` with `B = F_3`. The rank-four
    step is the signed comparison, and the refinement step is characteristic-free.
  * **Hexagon.** (SPG2) of `steinberg-group-is-glued-over-the-permutohedron` at `n = 3`. Each root is positive on three
    consecutive orders, so the adjacent identifications generate all of them.
  * **Trust.** Khanh arXiv:2609.08428v1 is unrefereed. The ternary case is conditional on
    `khanh-acyclicity-and-steinberg-criteria`. The proof of Voronetsky's Proposition 1 was not re-derived.
