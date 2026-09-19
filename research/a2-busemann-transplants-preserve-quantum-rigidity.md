---
rg: 2
id: a2-busemann-transplants-preserve-quantum-rigidity
kind: claim
title: Over lattices of thick Ã2 buildings, Busemann transplants of cone-deterministic fibres are quantum rigid iff the fibre is, and free when it is; far germ events are sector cylinders at the tile's own site, and projective-plane uniqueness transports them forward
distinct_from:
  busemann-transplants-of-rigid-z2-sfts-are-quantum-rigid: that poses the transfer for all Euclidean building lattices with the centrality step (C) open; this proves (C) and the transfer for Ã2, where the germ events are not chains, by a different mechanism.
  tree-product-busemann-transplants-preserve-quantum-rigidity: that proves the transfer for products of trees through monotone arrow chains; Ã2 germs form no chains, and here centrality comes from forward determination of sector cylinders by the link geometry, which also reproves the tree case.
  a2-lattice-boundary-skew-shifts-are-quantum-rigid: that gives a rigid but only topologically free SFT over Ã2 lattices; this uses it as the skeleton and decorates it into a free SFT, with rigidity reduced to a Z^2 fibre.
---

**ESTABLISHED** through `a2-busemann-transplant-rigidity-proof` (lane bh-invent-04, 2026-09-18;
elementary and algebraic lane proof, one adversarial referee PASS (see Referee); no priority claimed). It is conditional only on the
lane proofs it cites. Quantum families (Q1–Q3) are as in
`fp-v-times-subshift-full-groups-force-quantum-rigidity`. Nothing below restricts `dim W` or `char k`.

## Setting

- `Δ` is a locally finite thick Ã2 building. `Γ ≤ Aut(Δ)` is torsion-free and type-preserving, and it
  acts simply transitively on the vertices `V_0` of one type. Example: the index-3 type-preserving
  subgroups of the torsion-free CMSZ groups. These are finitely presented, one-ended and Kazhdan.
- `Ω` is the space of chambers at infinity, and `c ∈ Ω`.
  - In an apartment containing the sector `Q(v, c)`, write `Q(v, c) = v + Na + Nb`, where `a, b` are
    the unit vectors along its two walls.
  - `b_c : V_0 -> L` are the Busemann coordinates, and `C° ⊆ L` is the open cone.
  - `p_ℓ(v)` is the vertex of `Q(v, c)` at offset `ℓ`.
- **Skeleton.** The skeleton `X_s` is one of:
  - (i) the radius-`K` sector coding `X_Ω^K` of `busemann-transplants-give-free-sfts-on-building-lattices`,
    assuming (H_Ω) and that `X_Ω^K` is quantum rigid;
  - (ii) the finite skew product `P ⊆ Ω × Φ` of `a2-lattice-boundary-skew-shifts-are-quantum-rigid`,
    coded by radius-`K` sector germs together with the phase.

  In case (ii) no hypothesis is needed. `Γ ↷ P` is topologically free, and `F(G_V × (Γ ⋉ P))` is
  finitely presented. So `topologically-free-subshift-full-groups-force-quantum-rigidity`, which
  applies to every subshift coding, makes this coding an SFT that is rigid at all large scales.
- **Fibre.** `Λ_0` is any finitely generated group, and `M : Z^2 -> L` is an isomorphism.
  `Y ⊆ A^(Λ_0 × Z^2)` is an SFT that is **cone-deterministic** through `M`: there are a finite
  `W ⊆ Λ_0 × Z^2` with `Mu ∈ C°` for every `(w, u) ∈ W`, and a map `G` with
  `y(λ, z) = G( (y(λw, z + u))_{(w,u) ∈ W} )`.
  - Example: `Λ_0 = 1` and an NE-deterministic `Z^2`-SFT, with `M` chosen as in
    `busemann-transplants-give-free-sfts-on-building-lattices`.
  - `K` is at least every `|Mu|` (hexagonal norm) and at least `|w_0|`, for one fixed `w_0 ∈ L ∩ C°`.
    For skeleton (ii), `K` is also large enough that the radius-`K` germ reads off the phase change
    along every vertex of its sector piece.
- **Transplant.** `Y^Γ ⊆ (𝒜_s × A)^(Λ_0 × Γ)` consists of the pairs
  `(skeleton point over c, t)` with `t(λ, γ) = y(λ, M^(-1) b_c(γ o))` for some `y ∈ Y`.

## Theorem

1. **Finite type.** `Y^Γ` is an SFT, conjugate to the Busemann skew product over `X_s`
   (`busemann-transplants-give-free-sfts-on-building-lattices`, items 1–2, with `X_s` in place of
   `X_Ω`).
2. **Freeness.** `Λ_0 × Γ` acts freely on `Y^Γ` whenever `Λ_0 × Z^2` acts freely on `Y`. Here
   `γ ≠ 1` fixing `c` has a nonzero Busemann translation, by
   `chamber-fixing-building-lattice-elements-translate-horospheres`.
3. **Centrality (C).** In every `D`-quantum family for `Y^Γ` with `D >= max(D_s, K + R_0)`, every
   skeleton marginal commutes with every marginal at every site. Here `D_s` is the rigidity scale of
   `X_s`, and `R_0 = max_W |w|`.
4. **Rigidity.** If `Y` is `D_Y`-quantum rigid over `k`, then `Y^Γ` is `D`-quantum rigid over `k` for
   every `D >= max(D_s, K + R_0, κ + D_Y)`, with `μ = max_i |Me_i|` and `κ` the offset bound of
   Step 6 of the proof (`κ <= 3μ D_Y` when `M(N^2) ⊆ C̄`, e.g. for NE-deterministic `Y` with `M` as in the
   Setting's example). Distances on `Γ` are taken in the word metric of `{γ ≠ 1 : d(o, γo) <= 4}` (proof, metric
   convention). Conversely, if `Y^Γ` is rigid then so is `Y`, by
   `path-folded-sfts-are-quantum-rigid-only-if-the-fibre-is`.

## Corollaries

- **(a) The open transfer, for Ã2.** Under skeleton (i) this is the Statement of
  `busemann-transplants-of-rigid-z2-sfts-are-quantum-rigid` for Ã2 lattices. Its step (C) holds.
- **(b) Unconditional form over Kazhdan lattices.** Use skeleton (ii) and the Kari–Papasoglu
  NE-deterministic aperiodic tile set as `Y`. Then every `Γ` of the Setting carries a **free** SFT. It
  is quantum rigid iff the Kari–Papasoglu tiling SFT is. By Carroll–Penland (recalled, not re-read)
  existence of strongly aperiodic SFTs passes to the CMSZ groups themselves.
- **(c) Gate G2 over one-ended Kazhdan groups.**
  `a2-lattice-boundary-skew-shifts-are-quantum-rigid` gave rigidity only in the topologically free
  form. Now:
  - a free, quantum-rigid SFT over a one-ended Kazhdan lattice follows from one free, rigid,
    NE-deterministic `Z^2`-SFT;
  - more generally, over `Λ_0 × Γ` it follows from a free rigid cone-deterministic SFT over
    `Λ_0 × Z^2`.

## Lesson for general BH

- **Cylinder transport.**
  - A skeleton event at a far vertex is a finite sum of *sector cylinders at the tile's own site*,
    by compactness of `Ω`.
  - A sector cylinder at `v` of radius `R` is the germ at `v` times a cylinder of radius `R - 1` at
    *each* forward expansion site. This is the Determination Lemma. In Ã2 it holds because two
    vertices of a projective-plane link at distance two have a unique common neighbour.
  - So centrality is proved by induction on the radius, entirely at the tile's own sites. Far
    commutation is never needed.
- **What it replaces.** This supersedes the chain mechanism of
  `tree-product-busemann-transplants-preserve-quantum-rigidity` as the general principle.
  - (C) holds for any skeleton whose cylinders are forward-determined along the decoration's
    expansion directions. It is a local property of the building's links.
- **Consequence.** Non-amenable, even Kazhdan, geometry is transparent to fibre rigidity: it gives the
  skeleton's rigidity and the action's freeness, while the fibre's rigidity problem passes through
  unchanged.
  - So, along Busemann transplants, G2 in free form over every Ã2 lattice and every lattice in a
    product of trees reduces to one amenable question: is some strongly aperiodic, cone-deterministic `Z^2`-SFT
    (Kari–Papasoglu, Lukkarila) quantum rigid?
  - The master route should aim its rigidity effort at that one `Z^2` question.

## Referee (bh-ref-kourovka-a, 2026-09-18): PASS, with two minor fixable gaps

I checked `a2-busemann-transplant-rigidity-proof` line by line, with the cylinder-transport
induction (Step 4) and the Determination Lemma (Step 2) in full.

- **Step 1.** `ρ` is well defined by the compactness step: for a commuting family, a pattern that is
  locally admissible but not globally admissible dies on a larger ball. (F1)–(F3) are correct, and
  (F2) holds because sector pieces at `v` separate points of `X_s`, phases included.
- **Step 2, the Determination Lemma.** It is correct.
  - `lk(u)` is the incidence graph of a projective plane, of girth 6. So two directions at link
    distance 2 have exactly one common neighbour, and the completions `(−b,a) ↦ a−b` and
    `(−a,b) ↦ b−a` are forced in the whole building.
  - The row fill needs row `t` up to `α = R` (distance `R − s` from `p`), and the column fill needs
    column `s` up to `β = R` (distance `R − t`). The four regions cover the sector.
  - So the input radius is `R − min(s,t) <= R − 1` exactly when `s, t >= 1`, i.e. when `Mu ∈ C°`.
  - The operator form `E_S(v) = P_g(v) X_(S,u)` is `ρ` of an identity of clopen sets, with a
    separate identity for each expansion site `p_u`.
- **Step 4, Claim(R−1) ⇒ Claim(R).** It is correct as written.
  - The base `R <= 2D` follows from (F3) and (Q2).
  - In the step, `E_S T' = P_g X T' = P_g T' X = T' P_g X`, by Claim(R−1) at `(λw, p_u)` and then
    (Q2), since the distance is at most `K + R_0 <= D`. So `E_S` commutes with `Φ`.
  - `E_S ⊑ P_g(v)` and Step 3 give `E_S T_a = E_S Φ = Φ E_S = T_a E_S`.
  - Only commutations within `D` are used, as claimed.
  - (F2) then puts every skeleton marginal into some `𝒞_v^R`, which proves (C).
- **Steps 5–7.** The coherence induction, the canonical chain (existence via an apartment containing
  `c`, and nesting) and the letter expansion are correct.

**Gaps.**
1. **(metric convention)** "Within distance `r`" is building distance on `V_0`, while (Q2) and the
   ball sums use the word metric of `Λ`. State a generating set for which `d_Γ(γ,γ') <= d_Δ(γo,γ'o)`.
   For example, `{γ : d(o,γo) <= 4}` works: every vertex is within 1 of a vertex of `V_0`, so each
   pair of consecutive steps along a building geodesic is one hop of length at most 4.
2. **(Step 6, (Q3))** The offsets `M(f_z + D_Y 𝟏)` lie in `C̄` only if `M(N²) ⊆ C̄`, i.e.
   `Me_1, Me_2 ∈ C̄`. The Setting does not assume this; it only assumes `Mu ∈ C°` on `W`.
   - Either add the hypothesis (it holds for the NE example and for the `M` of
     `busemann-transplants-give-free-sfts-on-building-lattices`),
   - or take `z_* = z_p − N u_*` with `Mu_* ∈ C°` and `N` large, and enlarge the constant
     `(3μ+1)D_Y` accordingly.

   The theorem is unaffected.

**Both gaps fixed by the referee (09-18).** In the proof node:
- the metric convention with `S_4` is now in the header, with the proof that `d_Γ <= d_Δ`;
- Step 6 now uses `z_* = z_p − N_0 u_*` and the offset bound `κ`.

Theorem item 4 above now states the threshold as `κ + D_Y`. That is at most the original
`(3μ + 1) D_Y` when `M(N²) ⊆ C̄`.

**Conditional on unrefereed lane proofs:**
- `a2-lattice-boundary-skew-shifts-are-quantum-rigid` and
  `topologically-free-subshift-full-groups-force-quantum-rigidity`, for skeleton (ii);
- `chamber-fixing-building-lattice-elements-translate-horospheres`, for freeness;
- the down-direction fold node, for the converse.

The claim that other building types work (via short galleries) was not checked.
