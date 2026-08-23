import GroupApproximation.Sofic.NormalKazhdanHyperlinearKilled
import GroupApproximation.Sofic.TorsionFreeFullMFRadical

/-!
# The operator-to-Hilbert--Schmidt shadow residual

An element belongs to `opToHSShadowResidual G` when every operator-norm
almost representation of `G` kills it in the associated normalized
Hilbert--Schmidt ultraproduct.  This is the subgroup denoted
`R_{∞→2}(G)` or `𝔖(G)` in the Shadow--Kleene saturation notes.

The file packages four facts used by the compiler:

* the shadow residual is normal;
* it is covariant under every group homomorphism (restriction of target
  microstates proves this direction);
* one shadow word brings its whole normal closure with it;
* if the image of that normal closure saturates a Kazhdan target, the target
  has full norm-MF residual.

The last step is an application of the already checked normal-Kazhdan moving
corner detector.  The Higman, free-product, and Hull existence statements
which manufacture the saturating homomorphism remain the external
group-theoretic boundary.
-/

namespace GroupApproximation

open scoped commutatorElement

variable {G H : Type} [Group G] [Group H]

/-- The universal normalized-HS shadow kernel of operator-norm almost
representations. -/
def opToHSShadowResidual (G : Type) [Group G] : Subgroup G where
  carrier := {x | ∀ (B : OpAlmostRepresentation G) (U : Ultrafilter ℕ)
    (hcof : (U : Filter ℕ) ≤ Filter.cofinite),
    (KazhdanCompressionCore.toAsymptoticUnitaryRepresentation B).toUltraproductHom
      hcof x = 1}
  one_mem' := by
    intro B U hcof
    exact map_one _
  mul_mem' := by
    intro x y hx hy B U hcof
    rw [map_mul, hx B U hcof, hy B U hcof, mul_one]
  inv_mem' := by
    intro x hx B U hcof
    rw [map_inv, hx B U hcof, inv_one]

@[simp] theorem mem_opToHSShadowResidual_iff (x : G) :
    x ∈ opToHSShadowResidual G ↔
      ∀ (B : OpAlmostRepresentation G) (U : Ultrafilter ℕ)
        (hcof : (U : Filter ℕ) ≤ Filter.cofinite),
        (KazhdanCompressionCore.toAsymptoticUnitaryRepresentation B).toUltraproductHom
          hcof x = 1 :=
  Iff.rfl

/-- Shadow bugs move forward along arbitrary homomorphisms.  An almost
representation of the target restricts along the homomorphism.  Injectivity
is needed only when one also wants the image word to remain nontrivial. -/
theorem map_opToHSShadowResidual_le (f : G →* H) :
    (opToHSShadowResidual G).map f ≤ opToHSShadowResidual H := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := hy
  change x ∈ opToHSShadowResidual G at hx
  rw [mem_opToHSShadowResidual_iff] at hx ⊢
  intro B U hcof
  exact hx (B.comap f) U hcof

/-- The shadow residual is fully invariant. -/
theorem opToHSShadowResidual_isFullyInvariant (G : Type) [Group G] :
    ∀ f : G →* G, (opToHSShadowResidual G).map f ≤ opToHSShadowResidual G :=
  map_opToHSShadowResidual_le

/-- The shadow residual is normal, since it is preserved by inner
automorphisms (equivalently, because it is an intersection of kernels). -/
instance opToHSShadowResidual_normal : (opToHSShadowResidual G).Normal := by
  constructor
  intro x hx g
  rw [mem_opToHSShadowResidual_iff] at hx ⊢
  intro B U hcof
  rw [map_mul, map_mul, map_inv, hx B U hcof]
  group

/-- A shadow word brings its entire normal closure into the shadow
residual. -/
theorem normalClosure_le_opToHSShadowResidual {w : G}
    (hw : w ∈ opToHSShadowResidual G) :
    Subgroup.normalClosure ({w} : Set G) ≤ opToHSShadowResidual G := by
  apply Subgroup.normalClosure_le_normal
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst x
  exact hw

/-- A normal Kazhdan subgroup of the shadow residual lies in the norm-MF
residual.  This is the named shadow-radical interface to the moving-corner
detector. -/
theorem normalKazhdan_le_normMFResidual_of_le_opToHSShadowResidual
    [Countable G] (K : Subgroup G) [K.Normal]
    (hT : HasKazhdanPropertyT.{0, 0} K)
    (hK : K ≤ opToHSShadowResidual G) :
    K ≤ normMFResidual G := by
  exact KazhdanCompressionCore.normalKazhdan_le_normMFResidual_of_hyperlinear_killed
    (opToHSShadowResidual G)
    (fun B U hcof x hx ↦
      (mem_opToHSShadowResidual_iff x).mp hx B U hcof)
    K hT hK

/-- A Kazhdan group whose whole underlying group is shadow-killed has full
norm-MF residual. -/
theorem normMFResidual_eq_top_of_opToHSShadowResidual_eq_top
    [Countable G] (hT : HasKazhdanPropertyT.{0, 0} G)
    (hshadow : opToHSShadowResidual G = ⊤) :
    normMFResidual G = ⊤ := by
  apply top_unique
  let K : Subgroup G := ⊤
  letI : K.Normal := by dsimp [K]; infer_instance
  have hTK : HasKazhdanPropertyT.{0, 0} K :=
    HasKazhdanPropertyT.of_mulEquiv Subgroup.topEquiv hT
  apply normalKazhdan_le_normMFResidual_of_le_opToHSShadowResidual K hTK
  rw [hshadow]

/-- If the image of a shadow word normally generates a target, then the
target shadow residual is all of the target. -/
theorem opToHSShadowResidual_eq_top_of_image_normalClosure_eq_top
    (f : G →* H) {w : G} (hw : w ∈ opToHSShadowResidual G)
    (hgen : Subgroup.normalClosure ({f w} : Set H) = ⊤) :
    opToHSShadowResidual H = ⊤ := by
  apply top_unique
  rw [← hgen]
  apply Subgroup.normalClosure_le_normal
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst y
  exact map_opToHSShadowResidual_le f (Subgroup.mem_map_of_mem f hw)

/-- **One-word shadow saturation, formal analytic endpoint.**

Once an external compiler supplies a homomorphism whose image of a shadow
word normally generates a countable Kazhdan target, that target has full
norm-MF residual. -/
theorem normMFResidual_eq_top_of_shadow_bug_saturation
    [Countable H] (f : G →* H) {w : G}
    (hw : w ∈ opToHSShadowResidual G)
    (hgen : Subgroup.normalClosure ({f w} : Set H) = ⊤)
    (hT : HasKazhdanPropertyT.{0, 0} H) :
    normMFResidual H = ⊤ := by
  apply normMFResidual_eq_top_of_opToHSShadowResidual_eq_top hT
  exact opToHSShadowResidual_eq_top_of_image_normalClosure_eq_top f hw hgen

/-- Subgroup-valued router form: if the image of a shadow-killed subgroup is
the whole Kazhdan output, the output has full norm-MF residual. -/
theorem normMFResidual_eq_top_of_shadow_subgroup_saturation
    [Countable H] (D : Subgroup G) (hD : D ≤ opToHSShadowResidual G)
    (f : G →* H) (hsat : D.map f = ⊤)
    (hT : HasKazhdanPropertyT.{0, 0} H) :
    normMFResidual H = ⊤ := by
  apply normMFResidual_eq_top_of_opToHSShadowResidual_eq_top hT
  apply top_unique
  rw [← hsat]
  exact (Subgroup.map_mono hD).trans (map_opToHSShadowResidual_le f)

/-! ## The explicit Fournier--Facio HNN shadow bug -/

namespace FournierFacioDefectData

variable {P : Type} {E : Type} [Group P] [Group E]
    (D : FournierFacioDefectData P E)

/-- The single displayed commutator in the Fournier--Facio HNN skeleton is
in the operator-to-HS shadow residual.  This extracts one word from the
previous subgroup-valued compression-defect theorem. -/
theorem witness_commutator_mem_opToHSShadowResidual :
    ⁅D.s, D.iota D.witness⁆ ∈ opToHSShadowResidual E := by
  rw [mem_opToHSShadowResidual_iff]
  intro B U hcof
  exact D.core.defectNormal_hyperlinear_killed B U hcof
    ⁅D.s, D.iota D.witness⁆ D.witness_commutator_mem_defectNormal

include D in
/-- The HNN data carry a genuinely nontrivial shadow bug, not merely a
possibly trivial universally killed word. -/
theorem exists_nontrivial_opToHSShadowBug :
    ∃ w : E, w ≠ 1 ∧ w ∈ opToHSShadowResidual E :=
  ⟨⁅D.s, D.iota D.witness⁆, D.witness_commutator_ne_one,
    D.witness_commutator_mem_opToHSShadowResidual⟩

end FournierFacioDefectData

end GroupApproximation
