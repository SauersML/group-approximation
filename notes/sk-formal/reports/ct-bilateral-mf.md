# Lane ct-bilateral-mf: simple_kazhdan_sofic_group.tex l.174–204 at bf961c128

Target: origin/main `simple_kazhdan_sofic_group.tex` at bf961c128 (340 lines, md5 7b3dc4ec92b4581553bc0dc2b0edcb99),
subsection "A finite tower detects every normal subgroup". Rows keyed `LINE:<l>@bf961c128`.

Split agreed with skf-consequences:
- ct-bilateral-mf: l.174–204, root detection up to κ₀ ≠ I on W.
- skf-consequences: l.205–228 (H_W, simplicity of GL_d(F₂), conjugation by κ₀, I_N, N = G).

Interface: `TowerCornerWitnessStatement`, landed by skf-consequences. It is exactly the output of l.204, in coordinates:
- U, W clopen, W ⊆ U nonempty, tower levels T^aU (|a| ≤ m) disjoint;
- k ∈ N, k ≠ 1, entries of k − I₃ and k⁻¹ − I₃ in B_m(U);
- κ₀ ≠ 1 over Fin 3 × Fin (2m+1), with E_aa(W)·k_pq·E_bb(W) = κ₀((p,a),(q,b))·E_ab(W).
I produce it.

Neighbouring owners (ROSTER-sk 18:58): ct-involution l.67–86, 102–113, 154–173 (clopen partitions l.79–82, ring
generators l.84–86, E_ab(W), B_m(U), eq:absorb); ms-compress-4 l.86–101, 114–117 (eq:elementary, Z(G) = {1}).

## Route verdict

The printed route (localized non-commuting root, then the tower corner) is not the route of any Pestov91 simplicity
carrier. `SplitSimplicity` goes through row annihilators and `hsplit`; `SimpleModCentre` and `SimpleModCentreCrossed` go
through local annihilation and a column matrix. Those are statement-level carriers of "N = G" only. The only step whose
route coincides with an existing carrier is l.185–187: the commuting coefficients form a subring.

## Sentence ledger

| l. | sentence (abridged) | carrier | status |
|---|---|---|---|
| 175 | Let 1 ≠ N ⊴ G, choose 1 ≠ g ∈ N | binder of the producer | structural |
| 176–177 | w ≥ 0 bounds the exponents of all entries of g, g⁻¹ | to build: exponent bound from `SkewMonoidAlgebra.support` / `ClopenCrossedProduct.exists_sum_coeff_mul_unit_zpow` | open |
| 178–180 | finite clopen partition 𝒫 refining the letter partition, C ∩ T^jC = ∅, 0<l\|j\|≤2w+3 | existence is l.79–82 (ct-involution); tools `Dynamics.exists_separated_clopen_cover`; consumed through a named Prop until it lands | open |
| 180–184 | some h = e_ij(s), s ∈ {e_C, e_C u, e_C u⁻¹}, does not commute with g | to build in TowerRootDetection | open |
| 185–187 | otherwise the commuting coefficients form a subring containing the generators, so g ∈ Z(G) = {1} | `Pestov91.SimpleModCentre.commutingSubring`, `mem_center_of_commute_elGen`; generators l.84–86 (ct-involution; tool `Pestov91.CrossedProductFG.eq_top_of_unit_mem`); Z(G) = {1} (ms-compress-4; tools `Pestov91.center_elementaryGroup_eq_bot_of_central_zero_or_one`, `Pestov91.central_zero_or_one_of_free_minimal`) | partial |
| 189–193 | each s lies in B_1(U), U a translate of C: e_C = E_00(C), e_C u = E_10(T⁻¹C), e_C u⁻¹ = E_{-1,0}(TC) | to build (ring identities in ClopenCrossedProduct) | open |
| 194 | k = [g,h] ∈ N ∖ {1}, m = w+1 | normality (`SimpleModCentre.normal_comm_mem_left`); k ≠ 1 from non-commuting | open |
| 195–196 | by eq:absorb, k − I₃ and k⁻¹ − I₃ ∈ M₃(B_m(U)) | eq:absorb is ct-involution's (l.166–173); to build over its named Prop | open |
| 196–197 | k = (1−e)I₃ + eke, e the unit of B_m(U) | to build in TowerCornerLocalization | open |
| 197–201 | the corner part is invertible, so a locally constant κ : U → GL_d(F₂), d = 3(2m+1) ≥ 9 | to build (coordinate form of B_m(U) ≅ M_{2m+1}(LC(U,F₂)), l.162–165, ct-involution) | open |
| 202–203 | a nonempty clopen W ⊆ U on which κ is a constant κ₀ ≠ I_d | to build; produces `TowerCornerWitnessStatement` | open |

## Modules (claimed)

- CLAIM l.175–194 GroupApproximation/Manuscript/SimpleKazhdanSofic/TowerRootDetection.lean
- CLAIM l.195–203 GroupApproximation/Manuscript/SimpleKazhdanSofic/TowerCornerLocalization.lean

## Progress log

- 09-13 19:1x: re-keyed from b965d63ba (old l.574–683) to bf961c128; split agreed; ledger landed.
