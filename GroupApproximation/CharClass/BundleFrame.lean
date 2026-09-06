import GroupApproximation.CharClass.BundleLocal

/-!
# Complex vector bundles in the projection model, IX: the standard fibre

`BundleLocal.lean`'s `totalTriv`/`projTriv` trivialize a bundle over an open
neighbourhood of `x₀` against the *abstract* fibre `fibreSet (p x₀)` /
`projFibreSet (p x₀)` at the base point. To match the campaign's stated
deliverable literally — `E(p)|_U ≅ U × ℂ^r` and `P(p)|_U ≅ U × ℂP^{r-1}`, with
`ℂ^r` and `ℂP^{r-1}` the *fixed* models `Fin r → ℂ` and `STW59.CP (r-1)` — one
more step is needed: an isometry identifying the abstract fibre with the
standard one.

## The isometry

Every star-projection `q` of trace `r` is `W Wᴴ` for an isometry
`W : Matrix ι (Fin r) ℂ` (`Wᴴ W = 1`), built by peeling rank-one summands off
`q` one at a time (`STW59.exists_rankOneProj_absorbed`, the same machinery
`STW59.exists_natCast_trace` uses) and collecting the peeled unit vectors as
the columns of `W`. This is exactly a Murray-von Neumann equivalence of `q`
with the projection `1 : Matrix (Fin r) (Fin r) ℂ`, stated with the isometry
made explicit because both fibre identifications below are read off it
directly: `v ↦ Wᴴ *ᵥ v` for the vector space, `r ↦ Wᴴ * r * W` for the
projective space.

## Manuscript status

Machinery. Certifies no manuscript step on its own.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass

open scoped Matrix
open GroupApproximation.STW59
open Bundle

section Isometry

variable {ι : Type} [Fintype ι]

/-! ### Existence of the standard frame -/

private theorem exists_isometry_aux (r : ℕ) (q : Matrix ι ι ℂ) (hq : IsStarProjection q)
    (hr : q.trace = (r : ℂ)) :
    ∃ W : Matrix ι (Fin r) ℂ, Wᴴ * W = 1 ∧ W * Wᴴ = q := by
  induction r generalizing q with
  | zero =>
      have hq0 : q = 0 := proj_eq_zero_of_trace_eq_zero hq (by exact_mod_cast hr)
      refine ⟨0, ?_, ?_⟩
      · ext i j
        exact i.elim0
      · simp [hq0]
  | succ r ih =>
      have hqne : q ≠ 0 := by
        intro h
        rw [h, Matrix.trace_zero] at hr
        have hne : ((r + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero r
        exact hne hr.symm
      obtain ⟨j0, hj0⟩ := exists_column_ne_zero hqne
      obtain ⟨x, hxu, hqP, hPq⟩ := exists_rankOneProj_absorbed hq hj0
      have hPproj : IsStarProjection (rankOneProj x) := isStarProjection_rankOneProj hxu
      have hsub : IsStarProjection (q - rankOneProj x) := isStarProjection_sub hq hPproj hqP hPq
      have htrsub : (q - rankOneProj x).trace = (r : ℂ) := by
        rw [Matrix.trace_sub, hr, trace_rankOneProj hxu]
        push_cast
        ring
      obtain ⟨W', hW'1, hW'2⟩ := ih (q - rankOneProj x) hsub htrsub
      have hqx : q *ᵥ x = x := by
        have h : (q * rankOneProj x) *ᵥ x = rankOneProj x *ᵥ x := congrArg (· *ᵥ x) hqP
        rwa [← Matrix.mulVec_mulVec, rankOneProj_mulVec_self hxu] at h
      have hW'inj : Function.Injective (fun v : Fin r → ℂ => W' *ᵥ v) := by
        intro v w hvw
        simp only at hvw
        have h2 : (W')ᴴ *ᵥ (W' *ᵥ v) = (W')ᴴ *ᵥ (W' *ᵥ w) := congrArg (fun u => (W')ᴴ *ᵥ u) hvw
        rwa [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hW'1, Matrix.one_mulVec,
          Matrix.one_mulVec] at h2
      have hWx0 : (W')ᴴ *ᵥ x = 0 := by
        apply hW'inj
        show W' *ᵥ ((W')ᴴ *ᵥ x) = W' *ᵥ (0 : Fin r → ℂ)
        rw [Matrix.mulVec_zero, Matrix.mulVec_mulVec, hW'2, Matrix.sub_mulVec, hqx,
          rankOneProj_mulVec_self hxu, sub_self]
      have hWx0' : ∀ k : Fin r, (∑ i, star (W' i k) * x i) = 0 := by
        intro k
        have h := congrFun hWx0 k
        rw [Matrix.mulVec_apply_eq_sum] at h
        simpa only [Matrix.conjTranspose_apply, Pi.zero_apply] using h
      have hxW'0 : ∀ k : Fin r, (∑ i, star (x i) * W' i k) = 0 := by
        intro k
        have h : star (∑ i, star (W' i k) * x i) = star (0 : ℂ) := congrArg star (hWx0' k)
        rw [star_sum, star_zero] at h
        have heq : ∀ i, star (star (W' i k) * x i) = star (x i) * W' i k := by
          intro i
          rw [star_mul', star_star, mul_comm]
        rwa [Finset.sum_congr rfl (fun i _ => heq i)] at h
      set W : Matrix ι (Fin (r + 1)) ℂ :=
        Matrix.of fun i => Fin.snoc (fun j : Fin r => W' i j) (x i)
      have hWcastSucc : ∀ (i : ι) (j : Fin r), W i j.castSucc = W' i j := by
        intro i j
        show Fin.snoc (fun j' : Fin r => W' i j') (x i) j.castSucc = W' i j
        exact Fin.snoc_castSucc _ _ _
      have hWlast : ∀ i : ι, W i (Fin.last r) = x i := by
        intro i
        show Fin.snoc (fun j' : Fin r => W' i j') (x i) (Fin.last r) = x i
        exact Fin.snoc_last _ _
      refine ⟨W, ?_, ?_⟩
      · ext j k
        have hentry : (Wᴴ * W) j k = ∑ i, star (W i j) * W i k := by
          rw [Matrix.mul_apply]
          exact Finset.sum_congr rfl fun i _ => by rw [Matrix.conjTranspose_apply]
        rw [hentry]
        refine Fin.lastCases ?_ (fun j' => ?_) j
        · refine Fin.lastCases ?_ (fun k' => ?_) k
          · have hs : (∑ i, star (W i (Fin.last r)) * W i (Fin.last r))
                = ∑ i, star (x i) * x i := Finset.sum_congr rfl fun i _ => by rw [hWlast]
            rw [hs, sum_star_mul_self hxu, Matrix.one_apply_eq]
          · have hs : (∑ i, star (W i (Fin.last r)) * W i k'.castSucc)
                = ∑ i, star (x i) * W' i k' :=
              Finset.sum_congr rfl fun i _ => by rw [hWlast, hWcastSucc]
            rw [hs, hxW'0 k', Matrix.one_apply_ne (Fin.castSucc_ne_last k').symm]
        · refine Fin.lastCases ?_ (fun k' => ?_) k
          · have hs : (∑ i, star (W i j'.castSucc) * W i (Fin.last r))
                = ∑ i, star (W' i j') * x i :=
              Finset.sum_congr rfl fun i _ => by rw [hWcastSucc, hWlast]
            rw [hs, hWx0' j', Matrix.one_apply_ne (Fin.castSucc_ne_last j')]
          · have hs : (∑ i, star (W i j'.castSucc) * W i k'.castSucc)
                = ∑ i, star (W' i j') * W' i k' :=
              Finset.sum_congr rfl fun i _ => by rw [hWcastSucc, hWcastSucc]
            have hs2 : (∑ i, star (W' i j') * W' i k') = ((W')ᴴ * W') j' k' := by
              rw [Matrix.mul_apply]
              exact Finset.sum_congr rfl fun i _ => by rw [Matrix.conjTranspose_apply]
            rw [hs, hs2, hW'1]
            by_cases hjk : j' = k'
            · rw [hjk, Matrix.one_apply_eq, Matrix.one_apply_eq]
            · rw [Matrix.one_apply_ne hjk,
                Matrix.one_apply_ne (fun hc => hjk (Fin.castSucc_injective r hc))]
      · ext i i'
        have hsum : (W * Wᴴ) i i' = ∑ j : Fin (r + 1), W i j * star (W i' j) := by
          rw [Matrix.mul_apply]
          exact Finset.sum_congr rfl fun j _ => by rw [Matrix.conjTranspose_apply]
        rw [hsum, Fin.sum_univ_castSucc]
        have hterm1 : (∑ j' : Fin r, W i j'.castSucc * star (W i' j'.castSucc))
            = ∑ j' : Fin r, W' i j' * star (W' i' j') :=
          Finset.sum_congr rfl fun j' _ => by rw [hWcastSucc, hWcastSucc]
        have hterm2 : W i (Fin.last r) * star (W i' (Fin.last r)) = x i * star (x i') := by
          rw [hWlast, hWlast]
        rw [hterm1, hterm2]
        have hW'mul : (∑ j' : Fin r, W' i j' * star (W' i' j')) = (W' * (W')ᴴ) i i' := by
          rw [Matrix.mul_apply]
          exact Finset.sum_congr rfl fun j' _ => by rw [Matrix.conjTranspose_apply]
        rw [hW'mul, hW'2]
        show (q - rankOneProj x) i i' + x i * star (x i') = q i i'
        rw [Matrix.sub_apply, rankOneProj_apply]
        ring

/-- **Every star-projection of rank `r` is `W Wᴴ` for an isometry `W`.** Built
by peeling rank-one summands off `q` one at a time; the peeled unit vectors
become the columns of `W`. -/
theorem exists_isometry_of_isStarProjection {q : Matrix ι ι ℂ} (hq : IsStarProjection q)
    (r : ℕ) (hr : q.trace = (r : ℂ)) :
    ∃ W : Matrix ι (Fin r) ℂ, Wᴴ * W = 1 ∧ W * Wᴴ = q :=
  exists_isometry_aux r q hq hr

/-- **A choice of standard frame** for `q`, of the rank named by `hr`. -/
noncomputable def stdFrame {q : Matrix ι ι ℂ} (hq : IsStarProjection q) (r : ℕ)
    (hr : q.trace = (r : ℂ)) : Matrix ι (Fin r) ℂ :=
  (exists_isometry_of_isStarProjection hq r hr).choose

theorem stdFrame_conjTranspose_mul {q : Matrix ι ι ℂ} (hq : IsStarProjection q) (r : ℕ)
    (hr : q.trace = (r : ℂ)) : (stdFrame hq r hr)ᴴ * stdFrame hq r hr = 1 :=
  (exists_isometry_of_isStarProjection hq r hr).choose_spec.1

theorem stdFrame_mul_conjTranspose {q : Matrix ι ι ℂ} (hq : IsStarProjection q) (r : ℕ)
    (hr : q.trace = (r : ℂ)) : stdFrame hq r hr * (stdFrame hq r hr)ᴴ = q :=
  (exists_isometry_of_isStarProjection hq r hr).choose_spec.2

end Isometry

/-! ### The projective fibre absorbs its ambient projection on the right too -/

section Absorb

variable {ι : Type} [Fintype ι]

theorem absorb_right_of_mem_projFibreSet {q : Matrix ι ι ℂ} (hq : IsStarProjection q)
    {r : Matrix ι ι ℂ} (hr : r ∈ projFibreSet q) : r * q = r := by
  have h := congrArg Matrix.conjTranspose hr.2.2.2
  rwa [Matrix.conjTranspose_mul, conjTranspose_eq_of_isStarProjection hq, hr.1] at h

end Absorb

/-! ### The two standard-model fibre identifications -/

section StdFibre

variable {ι : Type} [Fintype ι]

theorem fibreEquivPi_invFun_mem {q : Matrix ι ι ℂ} (hq : IsStarProjection q) (r : ℕ)
    (hr : q.trace = (r : ℂ)) (u : Fin r → ℂ) : stdFrame hq r hr *ᵥ u ∈ fibreSet q := by
  show q *ᵥ (stdFrame hq r hr *ᵥ u) = stdFrame hq r hr *ᵥ u
  have key : (stdFrame hq r hr * (stdFrame hq r hr)ᴴ) *ᵥ (stdFrame hq r hr *ᵥ u)
      = stdFrame hq r hr *ᵥ u := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, stdFrame_conjTranspose_mul hq r hr,
      Matrix.mul_one]
  rwa [stdFrame_mul_conjTranspose hq r hr] at key

/-- **`fibreSet q` is homeomorphic to `Fin r → ℂ`**, via the standard frame. -/
noncomputable def fibreEquivPi {q : Matrix ι ι ℂ} (hq : IsStarProjection q) (r : ℕ)
    (hr : q.trace = (r : ℂ)) : ↥(fibreSet q) ≃ₜ (Fin r → ℂ) where
  toFun v := (stdFrame hq r hr)ᴴ *ᵥ (v : ι → ℂ)
  invFun u := ⟨stdFrame hq r hr *ᵥ u, fibreEquivPi_invFun_mem hq r hr u⟩
  left_inv v := by
    apply Subtype.ext
    show stdFrame hq r hr *ᵥ ((stdFrame hq r hr)ᴴ *ᵥ (v : ι → ℂ)) = (v : ι → ℂ)
    rw [Matrix.mulVec_mulVec, stdFrame_mul_conjTranspose hq r hr]
    exact v.2
  right_inv u := by
    show (stdFrame hq r hr)ᴴ *ᵥ (stdFrame hq r hr *ᵥ u) = u
    rw [Matrix.mulVec_mulVec, stdFrame_conjTranspose_mul hq r hr, Matrix.one_mulVec]
  continuous_toFun := continuous_const.matrix_mulVec continuous_subtype_val
  continuous_invFun := (continuous_const.matrix_mulVec continuous_id).subtype_mk _

theorem projFibreEquivCP_toFun_mem {q : Matrix ι ι ℂ} (hq : IsStarProjection q) (d : ℕ)
    (hr : q.trace = ((d + 1 : ℕ) : ℂ)) (r : ↥(projFibreSet q)) :
    (stdFrame hq (d + 1) hr)ᴴ * (r : Matrix ι ι ℂ) * stdFrame hq (d + 1) hr ∈ cpSet d := by
  obtain ⟨hrH, hrr, hrtr, hqr⟩ := r.2
  refine ⟨?_, ?_, ?_⟩
  · simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hrH,
      Matrix.mul_assoc]
  · have hrq : (r : Matrix ι ι ℂ) * q = r := absorb_right_of_mem_projFibreSet hq r.2
    calc ((stdFrame hq (d + 1) hr)ᴴ * (r : Matrix ι ι ℂ) * stdFrame hq (d + 1) hr)
          * ((stdFrame hq (d + 1) hr)ᴴ * (r : Matrix ι ι ℂ) * stdFrame hq (d + 1) hr)
        = (stdFrame hq (d + 1) hr)ᴴ *
            ((r : Matrix ι ι ℂ) *
              ((stdFrame hq (d + 1) hr * (stdFrame hq (d + 1) hr)ᴴ) *
                ((r : Matrix ι ι ℂ) * stdFrame hq (d + 1) hr))) := by
          simp only [Matrix.mul_assoc]
      _ = (stdFrame hq (d + 1) hr)ᴴ *
            ((r : Matrix ι ι ℂ) * (q * ((r : Matrix ι ι ℂ) * stdFrame hq (d + 1) hr))) := by
          rw [stdFrame_mul_conjTranspose hq (d + 1) hr]
      _ = (stdFrame hq (d + 1) hr)ᴴ *
            (((r : Matrix ι ι ℂ) * q) * ((r : Matrix ι ι ℂ) * stdFrame hq (d + 1) hr)) := by
          simp only [Matrix.mul_assoc]
      _ = (stdFrame hq (d + 1) hr)ᴴ *
            (((r : Matrix ι ι ℂ) * (r : Matrix ι ι ℂ)) * stdFrame hq (d + 1) hr) := by
          rw [hrq, Matrix.mul_assoc]
      _ = (stdFrame hq (d + 1) hr)ᴴ * (r : Matrix ι ι ℂ) * stdFrame hq (d + 1) hr := by
          rw [hrr, Matrix.mul_assoc]
  · have step : ((stdFrame hq (d + 1) hr)ᴴ * (r : Matrix ι ι ℂ) *
        stdFrame hq (d + 1) hr).trace = (r : Matrix ι ι ℂ).trace := by
      calc ((stdFrame hq (d + 1) hr)ᴴ * (r : Matrix ι ι ℂ) * stdFrame hq (d + 1) hr).trace
          = (stdFrame hq (d + 1) hr *
              ((stdFrame hq (d + 1) hr)ᴴ * (r : Matrix ι ι ℂ))).trace :=
            Matrix.trace_mul_comm _ _
        _ = (stdFrame hq (d + 1) hr * (stdFrame hq (d + 1) hr)ᴴ *
              (r : Matrix ι ι ℂ)).trace := by simp only [Matrix.mul_assoc]
        _ = (q * (r : Matrix ι ι ℂ)).trace := by rw [stdFrame_mul_conjTranspose hq (d + 1) hr]
        _ = (r : Matrix ι ι ℂ).trace := by rw [hqr]
    rw [step, hrtr]

theorem projFibreEquivCP_invFun_mem {q : Matrix ι ι ℂ} (hq : IsStarProjection q) (d : ℕ)
    (hr : q.trace = ((d + 1 : ℕ) : ℂ)) (s : CP d) :
    stdFrame hq (d + 1) hr * (s : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) *
      (stdFrame hq (d + 1) hr)ᴴ ∈ projFibreSet q := by
  obtain ⟨hsH, hss, hstr⟩ := s.2
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hsH,
      Matrix.mul_assoc]
  · calc (stdFrame hq (d + 1) hr * (s : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) *
            (stdFrame hq (d + 1) hr)ᴴ) *
          (stdFrame hq (d + 1) hr * (s : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) *
            (stdFrame hq (d + 1) hr)ᴴ)
        = stdFrame hq (d + 1) hr *
            ((s : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) *
              (((stdFrame hq (d + 1) hr)ᴴ * stdFrame hq (d + 1) hr) *
                ((s : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) * (stdFrame hq (d + 1) hr)ᴴ))) := by
          simp only [Matrix.mul_assoc]
      _ = stdFrame hq (d + 1) hr *
            ((s : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) *
              ((1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) *
                ((s : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) *
                  (stdFrame hq (d + 1) hr)ᴴ))) := by
          rw [stdFrame_conjTranspose_mul hq (d + 1) hr]
      _ = stdFrame hq (d + 1) hr *
            (((s : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) *
              (s : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)) * (stdFrame hq (d + 1) hr)ᴴ) := by
          simp only [Matrix.one_mul, Matrix.mul_assoc]
      _ = stdFrame hq (d + 1) hr * (s : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) *
            (stdFrame hq (d + 1) hr)ᴴ := by rw [hss, Matrix.mul_assoc]
  · have step : (stdFrame hq (d + 1) hr * (s : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) *
        (stdFrame hq (d + 1) hr)ᴴ).trace
          = (s : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ).trace := by
      calc (stdFrame hq (d + 1) hr * (s : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) *
            (stdFrame hq (d + 1) hr)ᴴ).trace
          = ((stdFrame hq (d + 1) hr)ᴴ *
              (stdFrame hq (d + 1) hr * (s : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ))).trace :=
            Matrix.trace_mul_comm _ _
        _ = ((stdFrame hq (d + 1) hr)ᴴ * stdFrame hq (d + 1) hr *
              (s : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)).trace := by
            simp only [Matrix.mul_assoc]
        _ = ((1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) *
              (s : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)).trace := by
            rw [stdFrame_conjTranspose_mul hq (d + 1) hr]
        _ = (s : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ).trace := by rw [Matrix.one_mul]
    rw [step, hstr]
  · have key : (stdFrame hq (d + 1) hr * (stdFrame hq (d + 1) hr)ᴴ) *
        (stdFrame hq (d + 1) hr * (s : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) *
          (stdFrame hq (d + 1) hr)ᴴ)
        = stdFrame hq (d + 1) hr * (s : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) *
            (stdFrame hq (d + 1) hr)ᴴ := by
      calc (stdFrame hq (d + 1) hr * (stdFrame hq (d + 1) hr)ᴴ) *
          (stdFrame hq (d + 1) hr * (s : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) *
            (stdFrame hq (d + 1) hr)ᴴ)
          = (stdFrame hq (d + 1) hr * ((stdFrame hq (d + 1) hr)ᴴ * stdFrame hq (d + 1) hr)) *
              (s : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) * (stdFrame hq (d + 1) hr)ᴴ := by
            simp only [Matrix.mul_assoc]
        _ = stdFrame hq (d + 1) hr * (s : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) *
              (stdFrame hq (d + 1) hr)ᴴ := by
            rw [stdFrame_conjTranspose_mul hq (d + 1) hr, Matrix.mul_one]
    rwa [stdFrame_mul_conjTranspose hq (d + 1) hr] at key

/-- **`projFibreSet q` is homeomorphic to `ℂP^{d}`** for `q` of rank `d + 1`,
via the standard frame. -/
noncomputable def projFibreEquivCP {q : Matrix ι ι ℂ} (hq : IsStarProjection q) (d : ℕ)
    (hr : q.trace = ((d + 1 : ℕ) : ℂ)) : ↥(projFibreSet q) ≃ₜ CP d where
  toFun r := ⟨(stdFrame hq (d + 1) hr)ᴴ * (r : Matrix ι ι ℂ) * stdFrame hq (d + 1) hr,
    projFibreEquivCP_toFun_mem hq d hr r⟩
  invFun s := ⟨stdFrame hq (d + 1) hr * (s : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) *
      (stdFrame hq (d + 1) hr)ᴴ, projFibreEquivCP_invFun_mem hq d hr s⟩
  left_inv r := by
    apply Subtype.ext
    show stdFrame hq (d + 1) hr * ((stdFrame hq (d + 1) hr)ᴴ * (r : Matrix ι ι ℂ) *
        stdFrame hq (d + 1) hr) * (stdFrame hq (d + 1) hr)ᴴ = (r : Matrix ι ι ℂ)
    have hrq : (r : Matrix ι ι ℂ) * q = r := absorb_right_of_mem_projFibreSet hq r.2
    have hqr : q * (r : Matrix ι ι ℂ) = r := r.2.2.2.2
    calc stdFrame hq (d + 1) hr * ((stdFrame hq (d + 1) hr)ᴴ * (r : Matrix ι ι ℂ) *
          stdFrame hq (d + 1) hr) * (stdFrame hq (d + 1) hr)ᴴ
        = (stdFrame hq (d + 1) hr * (stdFrame hq (d + 1) hr)ᴴ) * (r : Matrix ι ι ℂ) *
            (stdFrame hq (d + 1) hr * (stdFrame hq (d + 1) hr)ᴴ) := by
          simp only [Matrix.mul_assoc]
      _ = q * (r : Matrix ι ι ℂ) * q := by rw [stdFrame_mul_conjTranspose hq (d + 1) hr]
      _ = r * q := by rw [hqr]
      _ = r := hrq
  right_inv s := by
    apply Subtype.ext
    show (stdFrame hq (d + 1) hr)ᴴ * (stdFrame hq (d + 1) hr *
        (s : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) * (stdFrame hq (d + 1) hr)ᴴ) *
      stdFrame hq (d + 1) hr = (s : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    calc (stdFrame hq (d + 1) hr)ᴴ * (stdFrame hq (d + 1) hr *
          (s : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) * (stdFrame hq (d + 1) hr)ᴴ) *
        stdFrame hq (d + 1) hr
        = ((stdFrame hq (d + 1) hr)ᴴ * stdFrame hq (d + 1) hr) *
            (s : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) *
            ((stdFrame hq (d + 1) hr)ᴴ * stdFrame hq (d + 1) hr) := by
          simp only [Matrix.mul_assoc]
      _ = (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) *
            (s : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) * 1 := by
          rw [stdFrame_conjTranspose_mul hq (d + 1) hr]
      _ = (s : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) := by rw [Matrix.mul_one, Matrix.one_mul]
  continuous_toFun :=
    ((continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const).subtype_mk _
  continuous_invFun :=
    ((continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const).subtype_mk _

end StdFibre

/-! ### Local triviality against the standard model -/

section LocalStd

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **`E(p)` is literally `U × ℂ^r` on a trivializing neighbourhood.** -/
noncomputable def Bundle.totalTrivStd (p : Bundle X ι) (x₀ : X) (r : ℕ)
    (hr : p.rank x₀ = r) :
    Bundle.Total (p.restrictTo (Bundle.trivSet p x₀)) ≃ₜ ↥(Bundle.trivSet p x₀) × (Fin r → ℂ) :=
  (p.totalTriv x₀).trans
    (Homeomorph.prodCongr (Homeomorph.refl _)
      (fibreEquivPi (p.isStarProjection x₀) r (by rw [Bundle.trace_eq_rank, hr])))

/-- **`P(p)` is literally `U × ℂP^{d}` on a trivializing neighbourhood**, when
`p` has rank `d + 1` at `x₀`. -/
noncomputable def Bundle.projTrivStd (p : Bundle X ι) (x₀ : X) (d : ℕ)
    (hr : p.rank x₀ = d + 1) :
    Bundle.Proj (p.restrictTo (Bundle.trivSet p x₀)) ≃ₜ ↥(Bundle.trivSet p x₀) × CP d :=
  (p.projTriv x₀).trans
    (Homeomorph.prodCongr (Homeomorph.refl _)
      (projFibreEquivCP (p.isStarProjection x₀) d (by rw [Bundle.trace_eq_rank, hr])))

end LocalStd

end CharClass
end GroupApproximation
