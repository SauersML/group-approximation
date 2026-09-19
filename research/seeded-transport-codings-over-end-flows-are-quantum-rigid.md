---
rg: 2
id: seeded-transport-codings-over-end-flows-are-quantum-rigid
kind: claim
title: A computation layer transported bijectively along space and along the end flow's second-child steps, and seeded at every other time step, is quantum rigid over every field on every module; its spine sheet carries one global choice, so it is unsplittable
distinct_from:
  causal-depth-localizes-quantum-noncommutativity: that shows seeded determination is classical at finite depth and leaves the infinite-depth residue open; this closes the residue for bijective transport rules, including the spine sheet, on every module.
  deterministic-extensions-of-rigid-sfts-are-rigid: that needs transport from every site in a monoid-generating set of directions; here a seed carries no information about its parent, so the transport breaks upward at every seed, and the downhill induction replaces it.
---

**ESTABLISHED** through `seeded-transport-rigidity-downhill-proof` (lane bh-g2-fixedpoint-b,
2026-09-18; elementary, algebraic, not reviewed; no priority claimed). Quantum families are as in
`fp-v-times-subshift-full-groups-force-quantum-rigidity`.

## Setting

- **Groups.** `H = <S_H>` is any finitely generated group, the *space*, for example `Γ_0 × F_n`.
  `F_m` (`m >= 2`) is the *time*. `Λ = H × F_m`.
- **Time flow.** `X_∂ = X_∂(F_m)` is the end shift, with rank-`i` children `ψ_i` as in
  `end-shift-path-covers-are-rigid-with-one-spine`.
- **Base.** The base is `B = Y ⊠ X_∂ ⊆ (A_H × S_m)^Λ`, with `Y` an `H`-SFT. Its `H`-letters are
  constant along `F_m`, and its flow letters are constant along `H`.
- **Coding.** `Z ⊆ (A_H × S_m × C)^Λ` is an SFT with base projection in `B` and three rules, all of
  radius `<= R`. Here `p` denotes the base pattern near the site, and `z = (λ, v')`.
  - **(Sp) space transport.** `c(λs, v') = α_s(p, c(λ, v'))` for every `s ∈ S_H`, with
    `α_s(p, ·) ∈ Sym(C)`.
  - **(Ti) time transport.** If `v'` is a rank-2 child, then `c(λ, v') = β(p, c(λ, parent(v')))`,
    with `β(p, ·) ∈ Sym(C)`.
  - **(Se) seeds.** Otherwise, `c(λ, v') = κ(p)`.
- **Hypothesis (B).** The base marginals of every `D`-family commute. This holds when `Y` is
  quantum rigid, by `free-group-boundary-shifts-are-quantum-rigid` and
  `quantum-rigidity-is-product-stable`.

## Theorem

Let `D >= max(R, r_Y, 1)`, where `r_Y` is the radius of the forbidden patterns of `Y`, and assume
(B). Every `D`-quantum family of `Z`, over every field and on every module of any dimension,
commutes. In detail:
1. **Downhill centrality.** Every flow marginal `P_s(z)` commutes with every computation marginal
   `C_c(z')`.
2. **Space centrality.** Every `H`-letter marginal commutes with every `C_c(z')`.
3. **Commutation.** All `C_c(z)` commute with each other.

**Unsplittable spine.**
- *From the theorem.* By the far-modification Lemma of
  `minimal-sfts-with-a-finite-modification-are-not-quantum-rigid`, read contrapositively, no
  configuration of `Z` has two modifications whose supports are more than `2D` apart. This covers
  modifications that also change the base.
- *Explicitly, over a fixed base point* `(y, η)`.
  - Off the sheet `H × ℓ_η`, every letter is fixed: follow the time chain up to its seed, then
    apply `β` back down.
  - The sheet is nonempty only for `η ∈ Σ_ν`. There, (Sp) and (Ti) are bijective in both directions
    along `S_H` and `ℓ_η`, and the sheet is connected. So a completion is fixed by its letter at one
    site, and the sheet carries at most `|C|` global choices.

## Instances

- **The spine bit.** `C = {0,1}`, `α = β = id`, `κ = 1`. Anchored sites read `1`, and the spine sheet is
  constant, `0` or `1`.
- **Clocks.** `C = Z/q`, `α = id`, `β(c) = c + 1`, `κ = 0`. The letter is the time index mod `q` on
  anchored lines, and a global phase on the spine sheet. This is `C_Z` (…`++*−−`…) of synthesis v6,
  read along second-child time. The seeds are rank-1 children; the unseeded part is the spine, like the
  limit points `±∞`.
- **Data-dependent phases.** `α_s(p, c) = c + a_s(p)` over `Z/q`, with `a` a coboundary along each time
  slice. The phase then follows a function of the space data, up to one global constant.

All of these are *functional* (graph) phase couplings. They fall under cases (ii) and (iii) of the
phase-field trichotomy in `nonamenable-products-have-minimal-sft-extensions-of-free-inputs`, which is
a heuristic sketch there.

## Lesson for general BH

v6 says that rigid seeds get their rigidity from monotone chains toward the seed. This theorem is that
mechanism in operator form, for seeded coordinates of any finite phase type.
- **The downhill step.** Following the time flow up from a site either approaches a target site, and
  then induction applies, or it leaves it. In the second case the target lies below, and its flow
  letter is forced. No invariance or expansivity of the fibre is needed.
- **Consequence for E1 ∧ E2.** Functional phase fields are always rigid, and the spine costs nothing.
  - **Correction (same day).** An earlier version expected graph couplings to kill minimality, from
    the heuristic trichotomy. Over the end flow that is false.
  - `relational-spine-couplings-are-splittable-or-not-minimal` proves that the functional clock is
    minimal. It also proves that every relational coupling either splits or is not minimal.
  - What these codings still lack is input complexity, which is v6's CAP question.

## Referee (bh-ref-kourovka-a, 2026-09-18): PASS

I checked `seeded-transport-rigidity-downhill-proof` line by line.

- **Step 0.**
  - `ι` is a homomorphism onto `𝒜`, by (B), and `Y_D ⊆ B`, since the rules of `B` have radius
    `<= D`. So cylinder implications on `B` hold in `𝒜`.
  - Constancy follows by ball sums and adjacency.
  - (Sp\*) uses bijectivity of `α_s`: the ball-sum identity is `[p]C_c(λ) = [p]C_(α(c))(λs)` in both
    directions.
  - (Ti\*) holds for any `β` in the summed form `[p]C_c(z) = Σ_(β(g)=c) [p]C_g(parent)`. So the
    Remark that bijectivity of `β` is not used is correct.
- **Step 1, downhill induction.**
  - Seed and toward terms are immediate.
  - Away terms: if the arrow at `v'` points away from `a_1`, then on `B` the arrow at `w'` points
    along the geodesic toward `v'`. This is an implication of cylinders on `B`, so `[p]b = δ[p]`
    in `𝒜`. With `[p]X = X[p]`, this gives `[[p]X, b] = 0`.
- **Step 2.** Induction on `d_H` via (Sp\*) is correct.
- **Step 3.**
  - The reduction to one space coordinate uses central `𝒜`.
  - In the away case, `[p]` forces `parent(a_j) = a_(j−1)` along the geodesic. Expanding upward kills
    every other parent, so `[p]C(μ,u') ∈ alg(𝒜, C(μ,v'))`.
  - `X` sits at a neighbour of `(μ,v')`, so it commutes with that algebra.

The theorem holds over every field, on modules of any dimension.

**Not checked:**
- the "Unsplittable spine" paragraph, which rests on the far-modification Lemma of
  `minimal-sfts-with-a-finite-modification-are-not-quantum-rigid`;
- the Instances;
- hypothesis (B)'s citation to `quantum-rigidity-is-product-stable`.
