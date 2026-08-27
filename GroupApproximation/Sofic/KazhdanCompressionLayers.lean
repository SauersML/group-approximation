import GroupApproximation.Sofic.NormalKazhdanMFRadical
import GroupApproximation.Sofic.TelescopeRadicalInduction
import GroupApproximation.Sofic.UniversalFactorization

/-!
# Iterated Kazhdan compression layers

A one-sided compression obstruction need not account for the whole MF radical
at once.  Once a normal subgroup has entered the radical, every matrix-corona
representation factors through the corresponding quotient.  A new compression
obstruction in that quotient can therefore be pulled back to the original
group.  Repeating this observation gives a quotient tower whose successive
Kazhdan layers all lie in the radical of the source.

This has two endpoint forms.

* If the stage kernels exhaust the source, the source has full MF radical.
* If the tower converges to an MF quotient and the limit kernel is the union of
  the stage kernels, that limit kernel is exactly the MF radical.

Only the individual layers are required to be normal Kazhdan subgroups of the
groups in which they occur.  The source and the accumulated kernel need not
have property `(T)`.
-/

namespace GroupApproximation
namespace KazhdanCompressionLayers

open TelescopeRadicalInduction

/-! ## One quotient layer -/

variable {E Q Γ : Type} [Group E] [Group Q] [Group Γ]

/-- Pull a normal Kazhdan compression layer back through a surjection whose
kernel is already MF-invisible.  This is the basic iteration step. -/
theorem comap_normalKazhdanLayer_le_coronaMFResidual
    [Countable Q]
    (φ : E →* Q) (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ coronaMFResidual E)
    (C : KazhdanCompressionCore Γ Q)
    (K : Subgroup Q) [K.Normal]
    (hT : HasKazhdanPropertyT.{0, 0} K)
    (hK : K ≤ C.defectNormal) :
    K.comap φ ≤ coronaMFResidual E := by
  rw [UniversalFactorization.coronaMFResidual_eq_comap φ hφ hker]
  exact Subgroup.comap_mono
    (C.normalKazhdan_le_coronaMFResidual K hT hK)

/-- Norm-ultraproduct form of the one-layer pullback. -/
theorem comap_normalKazhdanLayer_le_normMFResidual
    [Countable E] [Countable Q]
    (φ : E →* Q) (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ normMFResidual E)
    (C : KazhdanCompressionCore Γ Q)
    (K : Subgroup Q) [K.Normal]
    (hT : HasKazhdanPropertyT.{0, 0} K)
    (hK : K ≤ C.defectNormal) :
    K.comap φ ≤ normMFResidual E := by
  have hker' : φ.ker ≤ coronaMFResidual E := by
    rw [coronaMFResidual_eq_normMFResidual]
    exact hker
  have h := comap_normalKazhdanLayer_le_coronaMFResidual
    φ hφ hker' C K hT hK
  rwa [coronaMFResidual_eq_normMFResidual] at h

/-- If the quotient itself is a normal Kazhdan compression layer, then a
previously invisible kernel and that quotient together force full radical in
the source. -/
theorem coronaMFResidual_eq_top_of_full_quotient_layer
    [Countable Q]
    (φ : E →* Q) (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ coronaMFResidual E)
    (C : KazhdanCompressionCore Γ Q)
    (hT : HasKazhdanPropertyT.{0, 0} Q)
    (hfull : C.defectNormal = ⊤) :
    coronaMFResidual E = ⊤ := by
  have hTtop : HasKazhdanPropertyT.{0, 0} (⊤ : Subgroup Q) :=
    HasKazhdanPropertyT.of_mulEquiv Subgroup.topEquiv hT
  have h := comap_normalKazhdanLayer_le_coronaMFResidual
    φ hφ hker C (⊤ : Subgroup Q) hTtop (by rw [hfull])
  exact top_unique (by simpa using h)

/-! ## Towers -/

variable {W : Type} [Group W]
variable {V : ℕ → Type} [∀ n, Group (V n)] [∀ n, Countable (V n)]
variable {Γs : ℕ → Type} [∀ n, Group (Γs n)]

/-- Every stage kernel of a quotient tower lies in the source MF radical when
each connecting kernel is contained in a normal Kazhdan compression layer of
the stage from which it starts. -/
theorem ker_stage_le_coronaMFResidual
    (T : Tower W V)
    (hbase : (T.stage 0).ker ≤ coronaMFResidual W)
    (hsurj : ∀ n, Function.Surjective (T.stage n))
    (C : ∀ n, KazhdanCompressionCore (Γs n) (V n))
    (K : ∀ n, Subgroup (V n))
    (hnormal : ∀ n, (K n).Normal)
    (hT : ∀ n, HasKazhdanPropertyT.{0, 0} (K n))
    (hK : ∀ n, K n ≤ (C n).defectNormal)
    (hstep : ∀ n, (T.step n).ker ≤ K n) :
    ∀ n, (T.stage n).ker ≤ coronaMFResidual W := by
  have hstepResidual :
      ∀ n, (T.step n).ker ≤ coronaMFResidual (V n) := by
    intro n
    letI : (K n).Normal := hnormal n
    exact (hstep n).trans
      ((C n).normalKazhdan_le_coronaMFResidual (K n) (hT n) (hK n))
  intro n
  induction n with
  | zero => exact hbase
  | succ n ih =>
      have hpull := UniversalFactorization.coronaMFResidual_eq_comap
        (T.stage n) (hsurj n) ih
      intro x hx
      rw [hpull, Subgroup.mem_comap]
      apply hstepResidual n
      rw [MonoidHom.mem_ker,
        ← TelescopeRadicalInduction.stage_succ_apply T n x]
      exact MonoidHom.mem_ker.mp hx

/-- Norm-ultraproduct form of the stage theorem. -/
theorem ker_stage_le_normMFResidual
    [Countable W]
    (T : Tower W V)
    (hbase : (T.stage 0).ker ≤ normMFResidual W)
    (hsurj : ∀ n, Function.Surjective (T.stage n))
    (C : ∀ n, KazhdanCompressionCore (Γs n) (V n))
    (K : ∀ n, Subgroup (V n))
    (hnormal : ∀ n, (K n).Normal)
    (hT : ∀ n, HasKazhdanPropertyT.{0, 0} (K n))
    (hK : ∀ n, K n ≤ (C n).defectNormal)
    (hstep : ∀ n, (T.step n).ker ≤ K n) :
    ∀ n, (T.stage n).ker ≤ normMFResidual W := by
  have hbase' : (T.stage 0).ker ≤ coronaMFResidual W := by
    rw [coronaMFResidual_eq_normMFResidual]
    exact hbase
  have h := ker_stage_le_coronaMFResidual
    T hbase' hsurj C K hnormal hT hK hstep
  intro n
  rw [← coronaMFResidual_eq_normMFResidual]
  exact h n

/-- If every element is killed at some finite stage, the MF radical of the
source is the whole group.  No single stage need kill the whole source. -/
theorem coronaMFResidual_eq_top_of_exhaustive_layers
    (T : Tower W V)
    (hbase : (T.stage 0).ker ≤ coronaMFResidual W)
    (hsurj : ∀ n, Function.Surjective (T.stage n))
    (C : ∀ n, KazhdanCompressionCore (Γs n) (V n))
    (K : ∀ n, Subgroup (V n))
    (hnormal : ∀ n, (K n).Normal)
    (hT : ∀ n, HasKazhdanPropertyT.{0, 0} (K n))
    (hK : ∀ n, K n ≤ (C n).defectNormal)
    (hstep : ∀ n, (T.step n).ker ≤ K n)
    (hexhaust : ∀ x : W, ∃ n, x ∈ (T.stage n).ker) :
    coronaMFResidual W = ⊤ := by
  have hstages := ker_stage_le_coronaMFResidual
    T hbase hsurj C K hnormal hT hK hstep
  rw [Subgroup.eq_top_iff']
  intro x
  obtain ⟨n, hx⟩ := hexhaust x
  exact hstages n hx

/-- Norm-ultraproduct form of exhaustive-layer collapse. -/
theorem normMFResidual_eq_top_of_exhaustive_layers
    [Countable W]
    (T : Tower W V)
    (hbase : (T.stage 0).ker ≤ normMFResidual W)
    (hsurj : ∀ n, Function.Surjective (T.stage n))
    (C : ∀ n, KazhdanCompressionCore (Γs n) (V n))
    (K : ∀ n, Subgroup (V n))
    (hnormal : ∀ n, (K n).Normal)
    (hT : ∀ n, HasKazhdanPropertyT.{0, 0} (K n))
    (hK : ∀ n, K n ≤ (C n).defectNormal)
    (hstep : ∀ n, (T.step n).ker ≤ K n)
    (hexhaust : ∀ x : W, ∃ n, x ∈ (T.stage n).ker) :
    normMFResidual W = ⊤ := by
  rw [← coronaMFResidual_eq_normMFResidual]
  have hbase' : (T.stage 0).ker ≤ coronaMFResidual W := by
    rw [coronaMFResidual_eq_normMFResidual]
    exact hbase
  exact coronaMFResidual_eq_top_of_exhaustive_layers
    T hbase' hsurj C K hnormal hT hK hstep hexhaust

/-- If the limit kernel is the union of the finite-stage kernels and the
limit group is MF, then the accumulated Kazhdan compression layers compute the
source MF radical exactly. -/
theorem coronaMFResidual_eq_ker_limit
    {P : Type} [Group P] [Countable P]
    (T : Tower W V)
    (hbase : (T.stage 0).ker ≤ coronaMFResidual W)
    (hsurj : ∀ n, Function.Surjective (T.stage n))
    (C : ∀ n, KazhdanCompressionCore (Γs n) (V n))
    (K : ∀ n, Subgroup (V n))
    (hnormal : ∀ n, (K n).Normal)
    (hT : ∀ n, HasKazhdanPropertyT.{0, 0} (K n))
    (hK : ∀ n, K n ≤ (C n).defectNormal)
    (hstep : ∀ n, (T.step n).ker ≤ K n)
    (limit : W →* P) (hlimit : Function.Surjective limit)
    (hunion : ∀ x ∈ limit.ker, ∃ n, x ∈ (T.stage n).ker)
    (hMF : IsOperatorMF P) :
    coronaMFResidual W = limit.ker := by
  have hstages := ker_stage_le_coronaMFResidual
    T hbase hsurj C K hnormal hT hK hstep
  have hker := TelescopeRadicalInduction.ker_limit_le_coronaMFResidual
    T limit hstages hunion
  exact TelescopeRadicalInduction.coronaMFResidual_eq_ker_limit
    limit hker hlimit
    ((isOperatorMF_iff_coronaMFResidual_eq_bot).mp hMF)

end KazhdanCompressionLayers
end GroupApproximation
