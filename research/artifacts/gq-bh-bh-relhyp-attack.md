# bh-relhyp: Boone--Higman for relatively hyperbolic groups (lane report, 2026-09-18)

Lane `bh-relhyp` of the BH swarm. Target: prove that a finitely generated
relatively hyperbolic group with solvable word problem and Boone--Higman peripheral
subgroups satisfies Boone--Higman, or locate the exact step that needs more.

## Outcome

Not proved. Three nodes landed:
- `rel-hyperbolic-groups-embed-with-fp-simple-peripherals` (ESTABLISHED, lane proof): any
  relatively hyperbolic `G` embeds in a relatively hyperbolic group whose peripheral
  subgroups are prescribed finitely generated overgroups of the old ones (Dahmani,
  Geom. Topol. 7 (2003), Theorem 0.1(2), read at source). With finitely presented
  simple overgroups the result is finitely presented when `G` is finitely presented
  relative to its peripherals.
- `rel-hyperbolic-bh-permanence-implies-free-product-closure` (ESTABLISHED, lane proof,
  elementary): the permanence statement implies free-product closure of the
  Boone--Higman class, which is equivalent on main to joint embedding plus
  `U * Z ∈ 𝓑` and is OPEN.
- `rel-hyperbolic-groups-with-bh-peripherals-satisfy-bh` (OPEN): the permanence
  statement, with known cases, the two reductions, and Attempt 1 stating the
  missing input (RB).

## Sources consulted

- Belk--Bleak--Matucci--Zaremsky, arXiv:2309.06224 (arXiv HTML): Theorems A, B, C, E;
  Proposition 5.5 (germ groups of contracting RSGs are virtually cyclic); Lemma 4.19
  (contracting lemma, where hyperbolicity is used); §1.3 open questions.
- Belk--Bleak--Matucci--Zaremsky, arXiv:2306.16356v3 (arXiv HTML): Theorem 5.1 list
  (items (5) limit groups and (8) finite-volume hyperbolic 3-manifolds), Problem 5.3
  items (1)--(13). Relatively hyperbolic groups are not mentioned.
- Dahmani, arXiv:math/0203258 (PDF): Theorem 0.1(1)--(3').
- Belk--Hyde--Matucci, arXiv:2407.03149 (TeX in the swarm source folder):
  `thm:MainFinitenessTheorem`, `cor:MainFinitenessCorollary`, `thm:Simplicity`,
  `thm:Abelianization`, and the Röver--Nekrashevych application.
- arXiv searches for "Boone-Higman" (17 results) and for "finitely presented simple"
  together with "relatively hyperbolic" (no results). No paper claiming this
  statement was found. No MathSciNet search.
- Belk--Fournier-Facio--Hyde--Zaremsky, arXiv:2503.21882 (abstract only):
  permutational Boone--Higman is closed under free products.

## Named consequences checked

- Limit groups: already BBMZ survey Theorem 5.1(5); also finitely generated linear.
- Finite-volume hyperbolic manifold groups: finitely generated linear, so
  `finitely-generated-linear-groups-satisfy-boone-higman`; dimension 3 is survey
  Theorem 5.1(8).
- Relatively hyperbolic 3-manifold groups: left to lane bh-3manifold, which owns
  compact 3-manifold groups.

## The precise open gate

(RB) in `rel-hyperbolic-groups-with-bh-peripherals-satisfy-bh`: a relative analogue of
BBMZ Theorem 4.1, realizing a group hyperbolic relative to finitely presented simple
groups inside a finite germ extension of a full contracting rational similarity
group, with the parabolic points as the singular set and germ groups `(B)_p × S_i`,
satisfying the Belk--Hyde--Matucci finiteness and simplicity hypotheses. Any such
construction for `S * T` would already give free-product closure.

## Update (free mode): amalgams over centralizers

Instead of building the germ-extension host (RB), the lane found an algebraic host.

**Construction.** For any group `G`, a finite set `F ⊆ G \ {1}` with `C = C_G(F)`, and
a subgroup `P ≤ G`, work in the relative holomorph `(G * <t>) ⋊ Aut_G(G * <t>)`.
- Let `μ_h` be the automorphism `t ↦ t h`.
- Let `c(h) = k(h) w k(h)`, with `k(h) = a_1(h) s ⋯ s a_k(h)` and
  `a_i(h) = t h z_i h^{-1} t^{-1}`.
- The conjugates `c(h) P c(h)^{-1}` depend only on `hC` and generate their free product.
- `μ(G)` permutes them like `G/C`.
- So `<μ(G), c(1) P c(1)^{-1}> ≅ G *_C (C × P)`.

**Landed (all lane proofs, not reviewed, no priority claimed):**
- `centralizer-amalgams-are-free-permutational-wreaths` (+ route): `A *_C (C × P)`
  is the free permutational wreath product, and it restricts to subgroups.
- `centralizer-amalgams-embed-in-relative-holomorphs` (+ route): the construction.
- `pbh-class-closed-under-centralizer-amalgams`: `M, P ∈ B_A` finitely generated
  implies `M *_{C_M(F)} (C_M(F) × P) ∈ B_A`. It has two routes:
  - via the landed relative-holomorph closure;
  - via BFFHZ Theorems C and E only.
- `cusp-extensions-of-torsion-free-hyperbolic-groups-satisfy-pbh`: `H *_{E(h)} (E(h) × P)`
  is hyperbolic relative to `E(h) × P` and embeds in a finitely presented simple group.
- `limit-groups-over-hyperbolic-groups-satisfy-boone-higman`: every finitely generated
  subgroup of the Lyndon completion `Γ^{Z[t]}` of `Γ` is in `B_A`. Here `Γ` is a
  torsion-free non-abelian hyperbolic group, or any Kharlampovich--Myasnikov class-`𝒢`
  group in `B_A`. The proof uses their JEMS 2012 Theorem C, read at source.
- An OPEN Attempt 2 on `rel-hyperbolic-groups-with-bh-peripherals-satisfy-bh`.

**Not landed (idea, unchecked).** A twisted version would handle
`G *_C (K ⋊ C)` for `K ≤ G` normalized by `C`. Conjugate by `c(h) t h`, and make
`c(h)` end in a `G`-letter so that `G_2`-letters are flanked correctly. Restricting to
`M ≤ G` then needs a copy of the action inside `G`. That works when `C_M(F)` is a
retract of `M`, which rarely gives anything beyond free products. It was aimed at
graph-manifold gluings: leaf pieces have non-primitive boundary curves, so neither
side retracts. Left for bh-3manifold.

## Update 2: torsion, graphs of groups, graph manifolds

**Landed (lane proofs, not reviewed):**
- `pbh-coset-condition-passes-to-finite-index-overgroups`: the indicator of a finite set of
  cosets gives the setwise stabilizer as a centralizer. Item 2 was also found independently
  as part 1 of `pbh-coset-wreath-subgroups-closure-properties`.
- `cusp-extensions-of-rel-hyperbolic-groups-satisfy-pbh`: cusps `E(g_i) × K_i` along
  non-commensurable loxodromic elements of any relatively hyperbolic `G ∈ B_A`, torsion
  allowed.
- `pbh-graphs-of-groups-over-realized-good-edges`: the graph-of-groups criterion stated
  below.
- `rel-hyperbolic-permanence-implies-finite-edge-amalgams`: calibration.

**The criterion.** A finite graph of groups lies in `B_A` if there are
- a group `D ∈ B_A`,
- embeddings `α_v : G_v → D`, and
- elements `w_e ∈ D`

such that `α_{e^-} ι_e^- = c_{w_e} ∘ α_{e^+} ι_e^+` on each `G_e`, and each edge image is
good in `D`. The proof maps `t_e ↦ s_e w_e` into the identity-edge multiple HNN of `D`
and checks Britton's lemma.

**Graph manifolds.** Use product pieces `V_v = F_v × <f_v>`. Passing to them needs a
finite cover; that step is a trust note and was not checked.

- *Two pieces, one torus.* Take `D = F_1 × F_2` with
  - `α_1(w f_1^k) = (w, ρ_1(w) ∂_2^{νk})`;
  - `α_2(w' f_2^k) = (λ_2(w') ∂_1^{pk}, w')`.

  Write the gluing as `f_2 = ∂_1^p f_1^q` and `∂_2 = ∂_1^r f_1^s`, with `Δ = ps − qr = ±1`.
  The torus condition then needs
  - `ρ_1(∂_1) = ∂_2^μ`, where `μ = −q/Δ` and `ν = p/Δ`;
  - `λ_2(∂_2) = ∂_1^r`;
  - `p ≠ 0`.

  With one boundary component per piece, each `∂_i` is a product of commutators. That
  forces `q = r = 0`, the flip gluing, and flip manifolds are already NPC (BBMZ survey,
  Theorem 5.1(7)). So nothing new comes from this `D`.
- *Obstruction for product ambient groups.* The fiber image `α_v(f_v)` lies in every
  torus at `v`, so every neighbour must reproduce its coordinates. That fails as soon as
  there are two neighbours, or two tori between the same two pieces: either
  `α_v(f_v) = 1`, or elements such as `[∂_e, ∂_{e'}]` die. So a working `D` cannot be a
  product of vertex-type factors.
- *Route left open.* Take an NPC graph manifold `M'` with the same pieces. Its group is
  virtually special, hence linear, hence in `B_A`. Realize each twist `τ_e ∈ GL_2(Z)`
  between the gluings of `M` and `M'` by an element that normalizes the torus in some
  faithful linear representation of `π_1(M')`. Adjoining these elements keeps `D`
  finitely generated and linear. What remains is keeping the tori good in the enlarged
  `D`. Not attempted; left for bh-3manifold.
