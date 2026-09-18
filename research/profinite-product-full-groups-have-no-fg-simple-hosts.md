---
rg: 2
id: profinite-product-full-groups-have-no-fg-simple-hosts
kind: claim
title: The full group of a profinite translation groupoid times any ample groupoid has no finitely generated simple subgroup containing the translations
distinct_from:
  fp-residually-finite-boone-higman: that is the open problem for all finitely presented residually finite groups; this kills one natural host shape for it, the Cantor hosts built by crossing the profinite translation action of G with a Thompson-type groupoid.
  bliw-locally-finite-tree-actions-embed-in-fp-simple-groups: that embeds groups acting on locally finite trees; this is about hosts inside topological full groups whose only link between the profinite coordinate and the expanding coordinate is the product structure.
  one-fp-simple-group-contains-every-brin-thompson-subgroup: that builds one twisted Brin--Thompson host from an action with finitely many pair orbits; this shows that the profinite translation action, crossed with any groupoid, cannot play that role.
---

**ESTABLISHED** (lane proof, elementary; not reviewed; no priority claimed).

**Setting.** `G` is an infinite finitely generated residually finite group and
`N_1 > N_2 > ...` a chain of finite-index normal subgroups with trivial
intersection. `Y = lim G/N_i` is the completion along the chain, a Cantor space on
which `G` acts freely by left translation. `ℋ` is any ample groupoid with unit space a
Cantor space `Z`, for example the Cuntz groupoid, whose full group is Thompson's `V`,
or a product of such. Put `𝒢 = (G ⋉ Y) × ℋ`, and embed `G` in the topological full
group `F(𝒢)` by `g ↦ ((y,z) ↦ (gy, z))`.

**Theorem.**
1. `F(𝒢) = ⋃_i F_i` is a strictly increasing union of proper subgroups, so it is not
   finitely generated. Here `F_i` is the subgroup of elements whose `G`-cocycle is
   constant on pieces of the form (`N_i`-coset) × (compact open subset of `Z`).
2. No finitely generated simple subgroup `S <= F(𝒢)` contains `G`.

**Proof.**
- *Cocycle.* Each `f ∈ F(𝒢)` has the local form `f(y,z) = (c_f(y,z) y, β(z))`, with
  `c_f` locally constant and `G`-valued, and `β` a local bisection of `ℋ`. Because `G`
  acts freely on `Y`, `c_f(y,z)` is determined by `f`.
- *The filtration.* Every clopen subset of `Y × Z` is a finite union of products
  `aN̂_i × W`, so `F(𝒢) = ⋃ F_i`. Left translation permutes `N_i`-cosets, since `N_i`
  is normal. So `f ∈ F_i` maps (`N_i`-coset) × (compact open) pieces to pieces of the
  same kind, and `F_i` is closed under composition and inverses.
- *Strictness.* Take `b ∈ N_i \ N_(i+1)`. The homeomorphism swapping `N̂_(i+1) × Z`
  and `bN̂_(i+1) × Z` by the translations `b` and `b^(-1)`, and fixing the rest, lies
  in `F_(i+1)`. Its cocycle takes different values on two `N_(i+1)`-cosets inside
  `N̂_i`, so it is not in `F_i`. Being finitely generated, `S` lies in some `F_i`.
- *A normal subgroup.* Let `K_i <= F_i` be the elements with cocycle values in `N_i`
  and trivial action on `Z`: `(y,z) ↦ (σ(yN_i, z) y, z)` with `σ` locally constant
  and `N_i`-valued. Conjugating by `f ∈ F_i` replaces `σ` by a conjugate
  `c σ c^(-1)`, which is again `N_i`-valued because `N_i` is normal. So `K_i` is
  normal in `F_i`, and `G ∩ K_i = N_i`. This uses that `g` acts trivially on
  `G/N_i` exactly when `g ∈ N_i`.
- *Simplicity.* Since the `F_i` increase, `S <= F_i` for some `i >= 1`. `S ∩ K_i` is
  normal in `S` and contains `N_i`, which is nontrivial because `G` is infinite and
  `N_i` has finite index. So `S <= K_i`, hence `G <= G ∩ K_i = N_i`, which is a proper
  subgroup of `G`. This is a contradiction.

**What this says for Problem 5.3(12).** A finitely presented simple host for a
residually finite `G` cannot be built by letting `G` act only through its profinite
translation action and adding expanding dynamics on an independent coordinate. The
expanding part must change the `G`-cocycle between depths of the completion. In a
finite Zappa--Szép (self-similar graph) product, that is a restriction map, that is a
virtual endomorphism. So such hosts reduce to the self-similar route
`fp-rf-boone-higman-via-fp-self-similar-overgroups`. For commensurator-rigid inputs,
injective virtual endomorphisms of finite-index image are also unavailable
(`commensurator-rigid-groups-have-no-faithful-bs-members`). This complements Attempt 4
on `fp-residually-finite-boone-higman`, which only ruled out type (A) actions from
the translation action.
