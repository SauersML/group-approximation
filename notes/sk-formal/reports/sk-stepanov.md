# sk-stepanov: simple_kazhdan_sofic_group.tex l.69–72, the Stepanov route to simplicity

Lane sk-stepanov: a fork launched 2026-09-13 ~20:15 by main (session nonsofic-existence-49; roster `ct/ROSTER-sk.md`, "OA LANES 20:15").
Note at origin e80dcf20a (386 lines, md5 4ad4921253626a4f858866c716a13385); census 09e580c38, row `bf137432ddb7`.

## CLAIM

CLAIM Stepanov Theorem 4.4, simple-ring case GroupApproximation/Algebra/StepanovNormalStructure.lean
CLAIM pair dependence by a dimension count on one cylinder GroupApproximation/Dynamics/ClopenCrossedProductPairDependence.lean
CLAIM printed l.69–72 endpoints GroupApproximation/Manuscript/SimpleKazhdanSofic/StepanovSimplicity.lean

Ownership check, 2026-09-13 20:2x:
- nothing on origin, in the shared tree, in `lanes/*.files` or in landed.log mentions Stepanov, pair dependence or the dimension count;
- ms-intro-3's ledger (row 69–72) lists the cylinder dimension count as its GAP but holds no file for it;
- main's roster assigns l.69–72 to this lane, and ms-intro-3 was told once.

## Ledger (tex l.69–72 at e80dcf20a)

| hash | sentence | carrier | status |
|---|---|---|---|
| `bf137432ddb7` | "Simplicity also follows from Stepanov's theorem on the normal structure of GL_n [Theorem 4.4], since the ring is simple and any two of its elements p,q satisfy pr+qs=0 with (r,s)≠0, by a dimension count on one cylinder." | the ring is simple: `SimpleKazhdanSofic.isSimpleRing` (RingSimpleCentre, landed); pair dependence: new, ClopenCrossedProductPairDependence; Theorem 4.4 for simple rings: new, StepanovNormalStructure; simplicity along this route: new, StepanovSimplicity | in progress |

## Route

1. **Dimension count** (`research/amenable-crossed-products-meet-stepanov-condition-b-proof`, Γ = ℤ).
   - Put the exponents of p and q in S ⊆ [−w, w], and take F = [0, 2w].
   - U is the common fibre, through one point, of the finitely many f_k∘T^m. It is clopen and nonempty; no compactness is needed.
   - r_ρ = Σ_g u^g (ρ_g e_U), and p r_ρ + q r_σ = Σ_m u^m (L(ρ,σ)_m e_U) with L : K^F × K^F → K^[−w,3w].
   - Since 2(2w+1) > 4w+1, L has a nonzero kernel vector. r_ρ = 0 forces ρ = 0 by the uniqueness of Laurent forms.
2. **Condition (b)** at I = 0: α = (0, r, s), b = 1, i = j = 0.
3. **Theorem 4.4** at the generality the sentence uses: R simple, so the only proper ideal is 0 and (a) is vacuous. The conclusion is part (3) of §1.6, with the repo's `relativeElementary` / `congruenceSubgroup` and uniqueness from `PreusserNormalizedBy.eq_of_sandwich`.
   - The proof follows p. 2152: d = c t_{*i}(αλ) c⁻¹ t_{*i}(−αλ).
   - Lemma 4.1 is used only at unit columns: in a subgroup without nontrivial transvections, a zero off-diagonal entry makes the element central, through column transvections.
   - At I = 0, simplicity of R takes the role of Lemma 4.3: β_p ≠ 0 and β_p R c'_{im} = 0 force c'_{im} = 0.
   - The transvection case uses `Pestov91.SimpleModCentre.normal_eq_top_of_elGen_mem` on `PreusserNormalizedBy.elementaryPart`.
4. **Simplicity.** `isSimpleGroup_of_preusser_sandwich` (CongruenceSubgroups) with the sandwich above, Z(R) = F₂ (RingSimpleCentre) and G infinite (ElementaryGroupFacts).
