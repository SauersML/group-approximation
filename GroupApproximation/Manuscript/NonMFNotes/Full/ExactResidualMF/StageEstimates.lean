import GroupApproximation.Manuscript.NonMFNotes.Full.ExactResidualMF.Stage
import GroupApproximation.Manuscript.NonMFNotes.Full.ExactResidualMF.RotationHoms

/-!
# One stage of the rotation construction

Source: `non_mf_group_notes.tex`, proof of `thm:exact-mf-residual`, and
Shulman (arXiv:2603.13564), proof of Theorem 10.  A stage is a finite set `Y`
with actions `act true`, `act false` of the two copies of `G` and a map
`ι : G *_Γ G → Y` intertwining left multiplication on the ball of radius
`2M + 1` (`StageCompatible`).  The layers are the images of the balls of
radii `M, …, 2M`, and the rotation angle is the layered potential of
`Stage.lean` with `M + 1` layers.

This file proves:

* `opLength_stage_le`: on `c ∈ Γ` with `c, c⁻¹` among the letters, the two
  families `pairHom` and its rotated conjugate differ by at most
  `π / (M + 1)` in operator norm;
* `colE_stage_true`, `colE_stage_false`: on the ball of radius `M` the
  rotation is a quarter turn, so letters of either copy follow the left
  multiplication of the double on basis vectors of the first sheet.
-/

namespace GroupApproximation.Full.NN01b

open GroupApproximation Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {G : Type} [Group G] {Γ : Subgroup G} {Y : FiniteModel}
variable (S : Finset G) (M : ℕ) (act : Bool → G →* Equiv.Perm Y) (ι : SymmetricDouble G Γ → Y)

/-- The local model intertwines left multiplication by letters on the ball of
radius `M + (M + 1)`. -/
def StageCompatible : Prop :=
  ∀ (b : Bool) (g : G) (x : SymmetricDouble G Γ), x ∈ dblBall G Γ S (M + (M + 1)) →
    inDouble G Γ b g * x ∈ dblBall G Γ S (M + (M + 1)) → act b g (ι x) = ι (inDouble G Γ b g * x)

/-- The `k`-th layer: the image of the ball of radius `M + k`. -/
def stageLayer (k : ℕ) : Set Y :=
  {w | ∃ x, x ∈ dblBall G Γ S (M + k) ∧ ι x = w}

theorem mem_stageLayer_iff {k : ℕ} {w : Y} :
    w ∈ stageLayer S M ι k ↔ ∃ x, x ∈ dblBall G Γ S (M + k) ∧ ι x = w :=
  Iff.rfl

theorem act_inv_apply (b : Bool) (g : G) (w : Y) : (act b g)⁻¹ w = act b g⁻¹ w :=
  congrArg (fun τ : Equiv.Perm Y => τ w) (map_inv (act b) g).symm

/-- A letter moves each layer into the next one. -/
theorem act_mem_stageLayer (hact : StageCompatible S M act ι) (b : Bool) {g : G} (hg : g ∈ S)
    {k : ℕ} (hk : k < M + 1) {w : Y} (hw : w ∈ stageLayer S M ι k) :
    act b g w ∈ stageLayer S M ι (k + 1) := by
  obtain ⟨x, hx, rfl⟩ := hw
  have hgx : inDouble G Γ b g * x ∈ dblBall G Γ S (M + (k + 1)) :=
    dblBall_mono (le_of_eq (Nat.add_assoc M k 1)) (letter_mem_dblBall b hg hx)
  rw [hact b g x (dblBall_mono (by omega) hx) (dblBall_mono (by omega) hgx)]
  exact (mem_stageLayer_iff S M ι).mpr ⟨_, hgx, rfl⟩

/-- Both shift conditions of the potential, for a letter whose inverse is a letter. -/
theorem stageLayer_shift (hact : StageCompatible S M act ι) (b : Bool) {g : G} (hg : g ∈ S)
    (hg' : g⁻¹ ∈ S) (w : Y) :
    (∀ k, k < M + 1 → w ∈ stageLayer S M ι k → (act b g)⁻¹ w ∈ stageLayer S M ι (k + 1)) ∧
      (∀ k, k < M + 1 → (act b g)⁻¹ w ∈ stageLayer S M ι k → w ∈ stageLayer S M ι (k + 1)) := by
  refine ⟨fun k hk hw => ?_, fun k hk hw => ?_⟩
  · rw [act_inv_apply]
    exact act_mem_stageLayer S M act ι hact b hg' hk hw
  · have hid : act b g ((act b g)⁻¹ w) = w := Equiv.apply_symm_apply (act b g) w
    rw [act_inv_apply] at hw hid
    exact Eq.mp (congrArg (fun v => v ∈ stageLayer S M ι (k + 1)) hid)
      (act_mem_stageLayer S M act ι hact b hg hk hw)

/-- Cosine of the stage angle. -/
def stageCos (w : Y) : ℝ := Real.cos (potAngle (stageLayer S M ι) (M + 1) w)

/-- Sine of the stage angle. -/
def stageSin (w : Y) : ℝ := Real.sin (potAngle (stageLayer S M ι) (M + 1) w)

theorem stage_hcs (w : Y) :
    stageCos S M ι w * stageCos S M ι w + stageSin S M ι w * stageSin S M ι w = 1 :=
  cos_mul_cos_add_sin_mul_sin (stageLayer S M ι) (M + 1) w

/-- The stage rotation. -/
def stageRot : Matrix.unitaryGroup (blockSumModel Y Y) ℂ :=
  rotUnitary Y (stageCos S M ι) (stageSin S M ι) (stage_hcs S M ι)

theorem stageCos_of_mem {x : SymmetricDouble G Γ} (hx : x ∈ dblBall G Γ S M) :
    stageCos S M ι (ι x) = 0 :=
  cos_potAngle_of_forall (stageLayer S M ι) (M + 1) (Nat.succ_ne_zero M) (ι x)
    fun k _ => (mem_stageLayer_iff S M ι).mpr ⟨x, dblBall_mono (Nat.le_add_right M k) hx, rfl⟩

theorem stageSin_of_mem {x : SymmetricDouble G Γ} (hx : x ∈ dblBall G Γ S M) :
    stageSin S M ι (ι x) = 1 :=
  sin_potAngle_of_forall (stageLayer S M ι) (M + 1) (Nat.succ_ne_zero M) (ι x)
    fun k _ => (mem_stageLayer_iff S M ι).mpr ⟨x, dblBall_mono (Nat.le_add_right M k) hx, rfl⟩

/-- **Stage commutator estimate** (`thm:exact-mf-residual`,
`non_mf_group_notes.tex`). -/
theorem norm_stage_commutator_le (hact : StageCompatible S M act ι) {c : G} (hcΓ : c ∈ Γ)
    (hc : c ∈ S) (hc' : c⁻¹ ∈ S) :
    ‖rotMatrix Y (stageCos S M ι) (stageSin S M ι) *
        blockDiagMatrix Y Y (pmat Y (act true c)) (pmat Y (act false c)) -
      blockDiagMatrix Y Y (pmat Y (act true c)) (pmat Y (act false c)) *
        rotMatrix Y (stageCos S M ι) (stageSin S M ι)‖ ≤
      2 * (Real.pi / 2 / ((M + 1 : ℕ) : ℝ)) := by
  refine norm_rotMatrix_commutator_le Y (stageCos S M ι) (stageSin S M ι) (act true c)
    (act false c) (potAngle_bound_nonneg (M + 1))
    (fun w => abs_cos_potAngle_sub_le (stageLayer S M ι) (M + 1) w _
      (stageLayer_shift S M act ι hact true hc hc' w).1
      (stageLayer_shift S M act ι hact true hc hc' w).2)
    (fun w => abs_cos_potAngle_sub_le (stageLayer S M ι) (M + 1) w _
      (stageLayer_shift S M act ι hact false hc hc' w).1
      (stageLayer_shift S M act ι hact false hc hc' w).2)
    (fun w => abs_sin_potAngle_sub_le (stageLayer S M ι) (M + 1) w _
      (stageLayer_shift S M act ι hact true hc hc' w).1
      (stageLayer_shift S M act ι hact true hc hc' w).2)
    (fun w => abs_sin_potAngle_sub_le (stageLayer S M ι) (M + 1) w _
      (stageLayer_shift S M act ι hact false hc hc' w).1
      (stageLayer_shift S M act ι hact false hc hc' w).2)
    fun w hw => ?_
  obtain ⟨k, hk, x, hx, rfl⟩ :=
    exists_mem_of_sin_potAngle_ne_zero (stageLayer S M ι) (M + 1) w hw
  have hx' : x ∈ dblBall G Γ S (M + (M + 1)) := dblBall_mono (by omega) hx
  have ht : inDouble G Γ true c⁻¹ * x ∈ dblBall G Γ S (M + (M + 1)) :=
    dblBall_mono (by omega) (letter_mem_dblBall true hc' hx)
  have hf : inDouble G Γ false c⁻¹ * x ∈ dblBall G Γ S (M + (M + 1)) :=
    dblBall_mono (by omega) (letter_mem_dblBall false hc' hx)
  rw [act_inv_apply, act_inv_apply, hact true c⁻¹ x hx' ht, hact false c⁻¹ x hx' hf]
  exact congrArg (fun y => ι (y * x)) (inDouble_agree G Γ ⟨c⁻¹, Γ.inv_mem hcΓ⟩ true false)

/-- **The two families almost agree on `Γ`** (`thm:exact-mf-residual`,
`non_mf_group_notes.tex`). -/
theorem opLength_stage_le (hact : StageCompatible S M act ι) {c : G} (hcΓ : c ∈ Γ)
    (hc : c ∈ S) (hc' : c⁻¹ ∈ S) :
    opLength (blockSumModel Y Y) ((pairHom Y (act true) (act false) c)⁻¹ *
        rotConjHom Y (stageRot S M ι) (pairHom Y (act true) (act false)) c) ≤
      2 * (Real.pi / 2 / ((M + 1 : ℕ) : ℝ)) :=
  (opLength_inv_mul_rotConjHom Y (stageRot S M ι) (pairHom Y (act true) (act false)) c).le.trans
    (norm_stage_commutator_le S M act ι hact hcΓ hc hc')

/-- Letters of the first copy follow the double on the ball of radius `M`. -/
theorem colE_stage_true (hact : StageCompatible S M act ι) (g : G) {x : SymmetricDouble G Γ}
    (hx : x ∈ dblBall G Γ S M) (hgx : inDouble G Γ true g * x ∈ dblBall G Γ S M) :
    ColE ((pairHom Y (act true) (act false) g : Matrix.unitaryGroup (blockSumModel Y Y) ℂ) :
        Matrix (blockSumModel Y Y) (blockSumModel Y Y) ℂ)
      (Sum.inl (ι x)) (Sum.inl (ι (inDouble G Γ true g * x))) := by
  have h := colE_pairHom Y (act true) (act false) g (ι x)
  rw [hact true g x (dblBall_mono (Nat.le_add_right M (M + 1)) hx)
    (dblBall_mono (Nat.le_add_right M (M + 1)) hgx)] at h
  exact h

/-- Letters of the second copy follow the double on the ball of radius `M`. -/
theorem colE_stage_false (hact : StageCompatible S M act ι) (g : G) {x : SymmetricDouble G Γ}
    (hx : x ∈ dblBall G Γ S M) (hgx : inDouble G Γ false g * x ∈ dblBall G Γ S M) :
    ColE ((rotConjHom Y (stageRot S M ι) (pairHom Y (act true) (act false)) g :
          Matrix.unitaryGroup (blockSumModel Y Y) ℂ) :
        Matrix (blockSumModel Y Y) (blockSumModel Y Y) ℂ)
      (Sum.inl (ι x)) (Sum.inl (ι (inDouble G Γ false g * x))) := by
  have heq : act false g (ι x) = ι (inDouble G Γ false g * x) :=
    hact false g x (dblBall_mono (Nat.le_add_right M (M + 1)) hx)
      (dblBall_mono (Nat.le_add_right M (M + 1)) hgx)
  have hc' : stageCos S M ι (act false g (ι x)) = 0 := by
    rw [heq]
    exact stageCos_of_mem S M ι hgx
  have hs' : stageSin S M ι (act false g (ι x)) = 1 := by
    rw [heq]
    exact stageSin_of_mem S M ι hgx
  have h := colE_rotConjHom Y (act true) (act false) (stageCos S M ι) (stageSin S M ι)
    (stage_hcs S M ι) g (ι x) (stageCos_of_mem S M ι hx) (stageSin_of_mem S M ι hx) hc' hs'
  rw [heq] at h
  exact h

end

end GroupApproximation.Full.NN01b
