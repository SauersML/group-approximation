---
rg: 2
id: copy-constraints-make-simulation-skeleton-and-data-commute
kind: claim
title: In a plane-constant simulation with an aligned rigid skeleton and uniform reading, every quantum family has commuting skeleton and data layers, whatever the growth of the simulated group
distinct_from:
  fp-v-times-subshift-full-groups-force-quantum-rigidity: that defines D-quantum families over a general group and derives rigidity from finite presentation of a full group; this proves that the copied and transported layers of a simulating SFT commute in every such family.
  effective-minimal-subshifts-lift-to-plane-constant-minimal-sfts: that is the open simulation statement (M1); this is about rigidity of any simulating SFT of that design, and does not construct one.
  sft-crossed-product-fp-iff-quantum-rigid: that equates rigidity with finite presentation of the Z^2 crossed product; this is a structural lemma about which idempotents of a quantum family must commute.
  bounded-determination-simulations-only-realize-sft-shadows: that is the companion dichotomy for the computation layer; this handles the skeleton and data layers.
---

**ESTABLISHED (lane proof, elementary, unreviewed; no priority claimed).** Lane bh-g1-rigidsim,
gate G1(h) of `research/artifacts/gq-bh-synthesis-master-route.md`.

## Setting

- `Λ_0` is finitely generated, with finite symmetric generating set `S_0`. Put `Λ = Λ_0 x Z^2`,
  with the word metric `d` for `S_0 x {0} ∪ {1} x {±e_1, ±e_2}`. Sites are `q = (λ, z)`.
- `X ⊆ A^Λ` is an SFT with forbidden patterns on balls of radius `D_X`. Its alphabet is layered:
  `A ⊆ H x B x C` (skeleton, data, computation).
- A *`D`-quantum family* `E_a(q)` over a field `k` is as in
  `fp-v-times-subshift-full-groups-force-quantum-rigidity`, conditions (Q1)–(Q3).
- For a layer `L` and a letter `ℓ` of that layer, the *layer projection* is
  `L_ℓ(q) = Σ_{a : a_L = ℓ} E_a(q)`. Layer projections at one site pairwise commute, and for each
  layer they form a partition of unity.

The design is the one proposed for (M1) in `effective-minimal-subshifts-lift-to-plane-constant-minimal-sfts`:
- **(Al) Alignment.** The rules of `X` force `x_H(λs, z) = x_H(λ, z)` for all `s ∈ S_0`.
- **(Cp) Copying.** The rules force `x_B(λ, z ± e_i) = x_B(λ, z)`.
- **(R1) Rigid skeleton.** `Ω_H = { z ↦ x_H(1, z) : x ∈ X } ⊆ H^(Z^2)` is a `Z^2`-SFT that is
  `D_H`-quantum rigid over `k`.
- **(R2) Uniform reading.** For every `r` there is `R(r)` with the following property. For all
  `λ, λ'` with `d(λ, λ') <= r` and every pattern `u` of `Ω_H` on `B_R(0) ⊆ Z^2`, there is a chain of
  sites `(λ', z_0) = q_0, q_1, ..., q_m`, pairwise adjacent, with `q_m` in plane `λ` and all
  `z`-coordinates in `B_R(0)`. The rules of `X` force the data letter at `q_0`, and then a register
  letter at each `q_i` (a coordinate of `C`), to be copied along the chain whenever the skeleton
  agrees with `u` within distance `D'` of the step. This is "zones in plane `λ` read `y(λ')`".

## Theorem

Let `D >= D_* := max(D_X, D_H, D' + 1)`. In every `D`-quantum family over `k`:
1. `H_h(λ, z) = H_h(1, z) =: H_h(z)` and `B_b(λ, z) = B_b(λ, 0) =: B_b(λ)` as operators.
2. All skeleton projections `H_h(z)` commute with each other.
3. Every `H_h(z)` commutes with every `B_b(λ)`.
4. All data projections `B_b(λ)` commute with each other.
5. Hence the skeleton and data projections generate a commutative algebra. Moreover `H_h(z)`
   commutes with every idempotent at any site `(μ, z')` with `|z - z'| <= 2D`, and `B_b(λ)` commutes
   with every idempotent at any site `(μ, z')` with `d(λ, μ) <= 2D`.

Only the finiteness of `R(r)` is used, never its size. **Exponential growth of `Λ_0`, and so the
"reading pressure" obstruction to (M1), has no effect on rigidity:** it can only obstruct existence.

## Proof

**Copy lemma.** Let `q, q'` be sites at distance `<= 2D`, and let `L, L'` be layers with the same
letters. Let `Π` be a product of layer projections at sites of one ball `pB_D ∋ q, q'`. Suppose no
`x ∈ X` carries the letters named by `Π` with `x_L(q) ≠ x_{L'}(q')`. Then `Π L_ℓ(q) = Π L'_ℓ(q')`.
- *Step 1.* Every factor lies in `pB_D`, so all factors commute (Q2). Expanding into full letters,
  `Π L_ℓ(q) L'_{ℓ'}(q')` with `ℓ ≠ ℓ'` is a sum of products over patterns on `pB_D` that do not occur
  in `X`, so it vanishes (Q3).
- *Step 2.* `Π L_ℓ(q) = Π L_ℓ(q) Σ_{ℓ'} L'_{ℓ'}(q') = Π L_ℓ(q) L'_ℓ(q')`.
- *Step 3.* Symmetrically, `Π L'_ℓ(q') = Π L_ℓ(q) L'_ℓ(q')`.

**Items 1–3.**
- *Item 1* is the copy lemma with `Π = I`, applied along (Al) and (Cp) and chained.
- *Item 3.* `H_h(z)` and `B_b(λ)` are layer projections at the common site `(λ, z)`.
- *Item 2.* The `H_h(z)` form a `D_H`-quantum family for `Ω_H`:
  - (Q1) is inherited;
  - (Q2) holds within `Z^2`-distance `2D >= 2D_H`;
  - (Q3) holds because a `B_{D_H}`-pattern `π` outside `L(Ω_H)` is the skeleton part of no pattern of
    `X` on the plane `{1} x (z + B_{D_H}) ⊆ (1, z)B_D`.
  Rigidity (R1) then makes them commute.

**Item 4.** Fix `λ, λ'` and `r = d(λ, λ')`, and put `R = R(r)`.
- *The partition.* For `u ∈ L_{B_R}(Ω_H)` let `Π_u = Π_{w ∈ B_R} H_{u(w)}(w)`, a commuting product by
  item 2. The skeleton projections generate a commutative algebra satisfying (Q1) and the (Q3)
  relations of `Ω_H`. It is therefore a quotient of `LC(Ω_H, k)`, in which the indicators of
  cylinders `[u]` sum to 1 and vanish exactly for `u ∉ L(Ω_H)`. So `Σ_u Π_u = I`.
- *The chain.* Fix `u` and a step `q_i → q_{i+1}` of its chain. Let `Σ_i` be the sub-product of
  `Π_u` over `|w - z_i| <= D'`. Read at plane `λ(q_i)`, its factors sit within `D' + 1 <= 2D` of
  `q_i` and `q_{i+1}`. The copy lemma gives `Σ_i R_i(q_i) = Σ_i R_{i+1}(q_{i+1})`. Since
  `Π_u = Π_u Σ_i`, chaining gives `Π_u B_c(λ') = Π_u T_c`, where `T_c` is the register projection at
  `q_m = (λ, z_m)`.
- *Commuting.* `T_c` and `B_{c'}(λ) = B_{c'}(λ, z_m)` sit at the same site, so they commute. By
  item 3, `Π_u` commutes with every data projection. Hence
  `Π_u B_c(λ') B_{c'}(λ) = Π_u T_c B_{c'}(λ) = B_{c'}(λ) Π_u T_c = Π_u B_{c'}(λ) B_c(λ')`.
- *Conclusion.* Summing over `u` gives `[B_c(λ'), B_{c'}(λ)] = 0`.

**Item 5.** The commutation ranges follow from item 1 and (Q2) at the relevant sites. ∎

## What this settles, and what it does not

- **Settled.** Neither the `Λ_0`-directions (alignment and inter-plane copying) nor the size of
  `Λ_0` contribute any non-commutativity. Of the three candidate obstructions listed for G1(h),
  *reading pressure* and *exponential growth* are irrelevant to rigidity.
- **Not settled.** The computation layer `C` is unconstrained here. The companion node
  `bounded-determination-simulations-only-realize-sft-shadows` shows that `C` cannot be a function of
  the skeleton and data in any simulation worth having. So every possible failure of rigidity sits in
  `C`, through *faults of the simulation layer*.

## Lesson for general BH

Everything a simulation copies is rigid for free: a copy rule is an exact operator identity in every
quantum family. That holds for skeleton alignment across `Λ_0`, data copied along the planes, and
data transported by wires. So the size and growth of `Λ_0` never harm rigidity. Only the finiteness
of reading radii is used. The crux G2 for simulations is entirely a property of the computation
layer, the computing hierarchy. `Λ_0` can still enter there, but only through the computation's
inter-plane messages, never through the copied layers.
