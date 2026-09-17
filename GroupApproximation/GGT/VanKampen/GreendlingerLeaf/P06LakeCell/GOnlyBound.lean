import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeCell.GOnlyStatement
import GroupApproximation.GGT.VanKampen.Estimating.PieceBridge
import GroupApproximation.GGT.VanKampen.Estimating.ShortSection
import GroupApproximation.GGT.VanKampen.SymmetricLabelAlphabet
import GroupApproximation.GGT.OsinTheorem54SepPolygon
import GroupApproximation.Meta.AxiomGuard

/-!
# Piece 06, case (d): a `G`-only filling bounds the complement arc

Lane `gl-p06-12` of `lanes/carto-gl-p06.md`.  This is the metric half of the `G`-only case: Osin,
arXiv:math/0411039v3, §9, proof of Lemma 9.7(b), the quasi-geodesic estimate of Lemma 9.6(a).
Infrastructure for `thm:hull`; certifies no printed sentence on its own.

## Statement

Let `A` be the complement of `t₁ = K.firstArc` in the boundary of `Π_i`: `t₁` followed by `A` is
the rotation of the boundary of `Π_i` that `t₁` starts (`IsComplementArc`).  Suppose the `G`-only
lake of `Π_i` fills `A`: the value of `A` equals the value of a dart word `σ` with `|σ| ≤ 2ε` (in the
model, `σ` is made of the `s`-parts of `K`).  Then
* `|A| ≤ λ⁻¹ (2ε + c)` (`cellArc_complement_short_of_gOnly`, first component);
* `|∂Π_i| ≤ |t₁| + λ⁻¹ (2ε + c)` (second component).

Proof: the rotation of `∂Π_i` is in `W` (`CyclicArc.cell_rotated_mem`) and is `(λ, c)`-quasi-geodesic
(`OsinCCondition.quasiGeodesic`).  Its prefix `A` gives `λ |A| - c ≤ ‖value A‖`.  The labels of `σ`
are letters of the symmetric alphabet (`hlabel`), which has the same word metric, so
`‖value σ‖ ≤ |σ| ≤ 2ε`.

## Why the filling is a hypothesis

The value equation `hval` is **not** derived from the case (d) hypotheses.  At fixed parameters it
can fail: if `∂Π_i` is vertex-pinched and the pocket holds `K`-parts, `Π_j` or relator cells, then
the value of `A` is a conjugate (see the FALSE-RISK item in `P06LakeCell/GOnlyStatement`).  The lemma
is strictly smaller in content than the `G`-only case: it gives only the length estimate, not an
exit.  It is true as stated: it is proved here, with no open input.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeCell

universe u w v

open Embedded GroupApproximation.HullSC GroupApproximation.WordMetric

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps rho : ℕ} {mu lambda c : ℝ} {X : DiscDiagram.{u, w, v} W}
  {i j : Fin X.rCellCount}

/-- **The complement arc of `K.firstArc`**: `t₁` followed by `A` is the rotation of the boundary of
`Π_i` that `t₁` starts. -/
def IsComplementArc (K : CellPocketFaceSet D eps X i j) (A : CyclicArc (cellDarts X i)) : Prop :=
  K.firstArc.darts ++ A.darts = K.firstArc.rotated

/-- The first arc and its complement arc cover the boundary of `Π_i`. -/
theorem length_add_of_isComplementArc (K : CellPocketFaceSet D eps X i j)
    (A : CyclicArc (cellDarts X i)) (hA : IsComplementArc K A) :
    K.firstArc.length + A.length = (cellDarts X i).length := by
  have h := congrArg List.length
    (show K.firstArc.darts ++ A.darts = K.firstArc.rotated from hA)
  rw [List.length_append, K.firstArc.darts_length, A.darts_length, K.firstArc.rotated_length] at h
  exact h

/-- **Quasi-geodesic lower bound for an arc of a cell**: an arc of `Π_i` is a prefix of a rotation of
the relator of `Π_i`, which lies in `W`. -/
theorem cellArc_quasi_lower (hcondition : OsinCCondition D W eps mu lambda c rho)
    (A : CyclicArc (cellDarts X i)) :
    lambda * (A.length : ℝ) - c ≤
      (wordNorm D.alphabet.carrier (RelLetter.listVal (dartWord X A.darts)) : ℝ) := by
  have hquasi := hcondition.quasiGeodesic _ (A.cell_rotated_mem hcondition.toIsSmallCancellation)
  have hlength : A.length ≤ (dartWord X A.rotated).length := by
    simpa only [dartWord, List.length_map, A.rotated_length] using A.length_le
  have h := hquasi.2 0 A.length (Nat.zero_le _) hlength
  have hprefix : (dartWord X A.rotated).take A.length = dartWord X A.darts := by
    simp only [dartWord, CyclicArc.darts, List.map_take]
  simpa only [Nat.sub_zero, OsinComponents.vertex_zero,
    OsinComponents.vertex_eq_mul_listVal_take, one_mul, hprefix,
    List.take_zero, RelLetter.listVal_nil, wordDist_one_left] using h

/-- **Length from norm**: an arc of a cell whose value has norm at most `2ε` has length at most
`λ⁻¹ (2ε + c)`. -/
theorem cellArc_length_le_of_norm_le (hcondition : OsinCCondition D W eps mu lambda c rho)
    (hlambda : 0 < lambda) (A : CyclicArc (cellDarts X i))
    (hnorm : wordNorm D.alphabet.carrier (RelLetter.listVal (dartWord X A.darts)) ≤ eps + eps) :
    (A.length : ℝ) ≤ lambda⁻¹ * (2 * (eps : ℝ) + c) := by
  have hupper : (wordNorm D.alphabet.carrier (RelLetter.listVal (dartWord X A.darts)) : ℝ) ≤
      2 * (eps : ℝ) := by
    exact_mod_cast (show wordNorm D.alphabet.carrier
      (RelLetter.listVal (dartWord X A.darts)) ≤ 2 * eps by omega)
  have hlower := cellArc_quasi_lower hcondition A
  rw [inv_mul_eq_div, le_div_iff₀ hlambda]
  nlinarith

/-- **Norm from a short filling**: if the value of `A` equals the value of a dart word `σ` with
`|σ| ≤ 2ε`, all of whose labels are letters of the symmetric alphabet, then the value of `A` has
norm at most `2ε`. -/
theorem cellArc_norm_le_of_value_eq
    (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d))
    (A : CyclicArc (cellDarts X i)) (σ : List X.toCombMap.Dart) (hσ : σ.length ≤ eps + eps)
    (hval : RelLetter.listVal (dartWord X A.darts) = RelLetter.listVal (dartWord X σ)) :
    wordNorm D.alphabet.carrier (RelLetter.listVal (dartWord X A.darts)) ≤ eps + eps := by
  have h := OsinComponents.wordNorm_listVal_le (symmetricLabelAlphabet D) (dartWord X σ) (by
    intro a ha
    simp only [dartWord, List.mem_map] at ha
    obtain ⟨d, _, rfl⟩ := ha
    exact hlabel d)
  rw [symmetricLabelAlphabet.wordNorm_eq] at h
  have hlen : (dartWord X σ).length = σ.length := by
    simp only [dartWord, List.length_map]
  rw [hval]
  omega

/-- **The complement arc of a `G`-only filled lake is short.**  Take the complement arc `A` of
`K.firstArc` and a `G`-only filling of `A` by a dart word `σ` with `|σ| ≤ 2ε`.  Then
`|A| ≤ λ⁻¹ (2ε + c)`, and so `|∂Π_i| ≤ |t₁| + λ⁻¹ (2ε + c)`. -/
theorem cellArc_complement_short_of_gOnly (hcondition : OsinCCondition D W eps mu lambda c rho)
    (hlambda : 0 < lambda) (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d))
    (K : CellPocketFaceSet D eps X i j) (A : CyclicArc (cellDarts X i)) (hA : IsComplementArc K A)
    (σ : List X.toCombMap.Dart) (hσ : σ.length ≤ eps + eps)
    (hval : RelLetter.listVal (dartWord X A.darts) = RelLetter.listVal (dartWord X σ)) :
    (A.length : ℝ) ≤ lambda⁻¹ * (2 * (eps : ℝ) + c) ∧
      ((cellDarts X i).length : ℝ) ≤ (K.firstArc.length : ℝ) + lambda⁻¹ * (2 * (eps : ℝ) + c) := by
  have hshort := cellArc_length_le_of_norm_le hcondition hlambda A
    (cellArc_norm_le_of_value_eq hlabel A σ hσ hval)
  refine ⟨hshort, ?_⟩
  have hsum := length_add_of_isComplementArc K A hA
  have hcast : ((cellDarts X i).length : ℝ) = (K.firstArc.length : ℝ) + (A.length : ℝ) := by
    exact_mod_cast hsum.symm
  rw [hcast]
  linarith

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeCell

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeCell.IsComplementArc
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeCell.length_add_of_isComplementArc
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeCell.cellArc_quasi_lower
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeCell.cellArc_length_le_of_norm_le
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeCell.cellArc_norm_le_of_value_eq
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeCell.cellArc_complement_short_of_gOnly
