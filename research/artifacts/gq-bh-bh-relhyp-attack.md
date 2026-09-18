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
