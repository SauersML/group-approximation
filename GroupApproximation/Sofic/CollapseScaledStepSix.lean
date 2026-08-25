import GroupApproximation.Sofic.CollapseTransportDiagonalizationCommutant
import GroupApproximation.Sofic.ScaledKazhdanTransport

/-!
# Step 6 of the involutive collapse, by the weighted transport theorem

## What this module certifies, and what it does not

`non_mf_groups_exist.tex` makes two different assertions about Step 6 of
`thm:collapse`, and they are not the same assertion.

* **The printed Step 6** transports inside the Hilbert-space ultraproduct
  `K_omega` of the `(M_{d_n}, Tr)`: the limiting cocycle is a coboundary
  `b(g) = y - pi(g) y`, `(W2)` puts `y` in `Fix pi(sLs⁻¹)`, and the *proof* of
  `thm:kazhdan-transport` supplies `Fix pi(sLs⁻¹) ⊆ Fix pi(L)` through `P`,
  `Q = pi(s) P pi(s)*`, `P ≤ Q` and `Q = P`.  **This development does not
  contain that route, and this module does not supply it.**  It cannot: the
  route needs `K_omega` as a genuine Hilbert space — `NormedAddCommGroup`,
  `InnerProductSpace ℝ`, `CompleteSpace` — and
  `Sofic/UltraproductModelConstruction.lean` builds the ultraproduct as a
  *module*, stating in its own docstring that the inner product and the
  Hilbert-space structure are deliberately not built.  `Delorme`'s fixed-point
  theorem sits in the repository, proved, with no `K_omega` to apply it to.
* **The rank-weight assertion**, printed in the discussion after
  that weighted transport theorem: "the collapse proof of Theorem `thm:collapse` uses
  a rank weight, which normalizes a defect at its own scale."  That is the
  assertion this module certifies, by actually invoking
  `ScaledKazhdanTransport.scaled_transport_both` at the weight `w_n = k_n`
  rather than re-deriving the transport inline.  It is audit row `R1` /
  `CO.14c`, together with `CO.14` and `CO.14b`.

So the record, stated plainly: **the route the Lean travels at Step 6 is the
rank-weight transport, not the ultraproduct argument that `thm:collapse`
prints.**  An accurate record of that divergence is the outcome here; a silent
divergence would not be.

## The three moves

The primitive of Step 5 almost commutes with the microstates of
`s iota(Gamma) s⁻¹` — a *proper* subgroup of `iota(Gamma)`, which is the
entire point of the compression — because `(W2)` makes the displacement vanish
exactly there.  Transport promotes that to `iota(Gamma)`:

1. `isScaledAsymptoticCommutantOf_of_conj_generating` — the rotated sequence
   `x_n = U_t* y_n U_t` lies in the scaled asymptotic commutant of `iota`
   itself.  Per generator this is `scaledMassVanishing_rotate`: the
   displacement of `x` against `U_{iota a}` is the displacement of `y` against
   `U_t U_{iota a} U_t*`, conjugated back, and `U_t U_{iota a} U_t*` differs
   from `U_{t iota a t⁻¹}` by an operator-norm null amount
   (`opNormVanishing_map_conj`), which
   `ScaledKazhdanTransport.scaled_conjugation_massVanishing_of_opNormVanishing`
   turns into a scaled-mass null difference at the weight.  Passing from the
   Kazhdan generators to all of `Gamma` is
   `CollapseTransportDiagonalizationCommutant.isScaledAsymptoticCommutantOf_of_generating`.
2. `scaled_transport_both` applies to `x`.
3. Its forward half returns `U_t x_n U_t*`, which is `y_n` **exactly**, by
   unitarity.  Nothing is lost in the round trip, so `y` itself lies in the
   scaled asymptotic commutant of `iota`.

The weight is never normalized by a dimension: it is carried as the parameter
`w`, and the collapse instantiates it at `w_n = k_n`, the rank normalization of
Step 3.
-/

namespace GroupApproximation
namespace CollapseScaledStepSix

open Matrix KazhdanCornerMatrices ScaledKazhdanTransport

open scoped Matrix.Norms.L2Operator

variable {Γ E : Type} [Group Γ] [Group E]

/-! ## Two facts about microstates -/

/-- Microstates are unitary, hence operator-norm contractions. -/
theorem norm_map_le_one (B : OpAlmostRepresentation E) (g : E) (n : ℕ) :
    ‖(B.map n g : Matrix (B.model n) (B.model n) ℂ)‖ ≤ 1 := by
  letI : Nonempty (B.model n) := Fintype.card_pos_iff.mp (B.modelNonempty n)
  exact le_of_eq (CStarRing.norm_of_mem_unitary (B.map n g).2)

/-- Conjugate transposes of microstates are unitary. -/
theorem conjTranspose_map_mem_unitaryGroup (B : OpAlmostRepresentation E)
    (t : E) (n : ℕ) :
    ((B.map n t : Matrix (B.model n) (B.model n) ℂ)ᴴ) ∈
      Matrix.unitaryGroup (B.model n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_conjTranspose]
  exact Unitary.star_mul_self_of_mem (B.map n t).2

/-! ## The conjugation defect -/

/-- **Microstates of a conjugate are asymptotically the conjugate of the
microstates.**  `U_{tgt⁻¹}` and `U_t U_g U_t*` differ by an operator-norm null
amount: three defects telescope — the two multiplicative ones, of `t g`
against `t⁻¹` and of `t` against `g`, and the inversion defect
`U_{t⁻¹} ≈ U_t*`. -/
theorem opNormVanishing_map_conj (B : OpAlmostRepresentation E) (t g : E) :
    OpNormVanishing B (fun n ↦
      (B.map n (t * g * t⁻¹) : Matrix (B.model n) (B.model n) ℂ) -
        (B.map n t : Matrix (B.model n) (B.model n) ℂ) *
          (B.map n g : Matrix (B.model n) (B.model n) ℂ) *
          (B.map n t : Matrix (B.model n) (B.model n) ℂ)ᴴ) := by
  have h1 := multiplicativeDefect_vanishing B (t * g) t⁻¹
  have h2 := (multiplicativeDefect_vanishing B t g).mul_right_of_norm_le_one
    (fun n ↦ (B.map n t⁻¹ : Matrix (B.model n) (B.model n) ℂ))
    (fun n ↦ norm_map_le_one B t⁻¹ n)
  have h3 := (map_inv_vanishing B t).mul_left_of_norm_le_one
    (fun n ↦ (B.map n t : Matrix (B.model n) (B.model n) ℂ) *
      (B.map n g : Matrix (B.model n) (B.model n) ℂ))
    (fun n ↦ by
      calc
        ‖(B.map n t : Matrix (B.model n) (B.model n) ℂ) *
            (B.map n g : Matrix (B.model n) (B.model n) ℂ)‖ ≤
            ‖(B.map n t : Matrix (B.model n) (B.model n) ℂ)‖ *
              ‖(B.map n g : Matrix (B.model n) (B.model n) ℂ)‖ :=
          Matrix.l2_opNorm_mul _ _
        _ ≤ 1 * 1 :=
          mul_le_mul (norm_map_le_one B t n) (norm_map_le_one B g n)
            (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1)
  exact ((h1.add h2).add h3).congr fun n ↦ by noncomm_ring

/-! ## Move 1: rotating the commutant relation back through the compressor -/

section Rotation

variable {B : OpAlmostRepresentation E} {w : ℕ → ℝ}
variable {y : ∀ n, Matrix (B.model n) (B.model n) ℂ}

/-- Rotating a mass-bounded sequence by a microstate preserves mass
boundedness at the same weight, with the same constant: conjugation by a
unitary is an exact isometry for the Frobenius mass. -/
theorem scaledMassBounded_rotate (t : E)
    (hbound : IsScaledMassBounded B w y) :
    IsScaledMassBounded B w (fun n ↦
      (B.map n t : Matrix (B.model n) (B.model n) ℂ)ᴴ * y n *
        (B.map n t : Matrix (B.model n) (B.model n) ℂ)) := by
  obtain ⟨Cm, hCm0, hCm⟩ := hbound
  refine ⟨Cm, hCm0, fun n ↦ ?_⟩
  have h := matMass_unitary_conj (conjTranspose_map_mem_unitaryGroup B t n)
    (y n)
  rw [Matrix.conjTranspose_conjTranspose] at h
  rw [h]
  exact hCm n

/-- **The rotation, one group element at a time.**  If the mass-bounded
sequence `y` has scaled-mass null displacement against `U_{t g t⁻¹}`, then the
rotated sequence `U_t* y U_t` has scaled-mass null displacement against `U_g`.

The rotation itself is exact — `U_t*(y - A y A*)U_t = x - U_g x U_g*` for
`A = U_t U_g U_t*`, by `U_t* U_t = 1` applied twice.  The only approximate step
is replacing `A` by `U_{t g t⁻¹}`, which is precisely the hypothesis of
`scaled_conjugation_massVanishing_of_opNormVanishing`. -/
theorem scaledMassVanishing_rotate (hw : ∀ n, 0 ≤ w n) (t g : E)
    (hbound : IsScaledMassBounded B w y)
    (hy : ScaledMassVanishing B w (fun n ↦
      y n -
        (B.map n (t * g * t⁻¹) :
            Matrix (B.model n) (B.model n) ℂ) * y n *
          (B.map n (t * g * t⁻¹) :
            Matrix (B.model n) (B.model n) ℂ)ᴴ)) :
    ScaledMassVanishing B w (fun n ↦
      ((B.map n t : Matrix (B.model n) (B.model n) ℂ)ᴴ * y n *
          (B.map n t : Matrix (B.model n) (B.model n) ℂ)) -
        (B.map n g : Matrix (B.model n) (B.model n) ℂ) *
          ((B.map n t : Matrix (B.model n) (B.model n) ℂ)ᴴ * y n *
            (B.map n t : Matrix (B.model n) (B.model n) ℂ)) *
          (B.map n g : Matrix (B.model n) (B.model n) ℂ)ᴴ) := by
  have hstar := conjTranspose_map_mem_unitaryGroup B t
  -- the conjugated microstate is unitary
  have hAmem : ∀ n : ℕ,
      (B.map n t : Matrix (B.model n) (B.model n) ℂ) *
          (B.map n g : Matrix (B.model n) (B.model n) ℂ) *
          (B.map n t : Matrix (B.model n) (B.model n) ℂ)ᴴ ∈
        Matrix.unitaryGroup (B.model n) ℂ :=
    fun n ↦ mul_mem (mul_mem (B.map n t).2 (B.map n g).2) (hstar n)
  -- replacing `U_{t g t⁻¹}` by `U_t U_g U_t*` costs a scaled-mass null term
  have hmix := scaled_conjugation_massVanishing_of_opNormVanishing hw
    (fun n ↦ B.map n (t * g * t⁻¹))
    (fun n ↦ (⟨_, hAmem n⟩ : Matrix.unitaryGroup (B.model n) ℂ))
    y hbound (opNormVanishing_map_conj B t g)
  -- so the displacement against the conjugated microstate is null
  have hAy : ScaledMassVanishing B w (fun n ↦
      y n -
        ((B.map n t : Matrix (B.model n) (B.model n) ℂ) *
            (B.map n g : Matrix (B.model n) (B.model n) ℂ) *
            (B.map n t : Matrix (B.model n) (B.model n) ℂ)ᴴ) * y n *
          ((B.map n t : Matrix (B.model n) (B.model n) ℂ) *
            (B.map n g : Matrix (B.model n) (B.model n) ℂ) *
            (B.map n t : Matrix (B.model n) (B.model n) ℂ)ᴴ)ᴴ) :=
    ((hy.add hmix).congr fun n ↦ by abel)
  have hrot := hAy.unitary_conjugate
    (fun n ↦ (⟨_, hstar n⟩ : Matrix.unitaryGroup (B.model n) ℂ))
  -- the rotation is exact
  have hid : ∀ n : ℕ,
      (B.map n t : Matrix (B.model n) (B.model n) ℂ)ᴴ *
          (y n -
            ((B.map n t : Matrix (B.model n) (B.model n) ℂ) *
                (B.map n g : Matrix (B.model n) (B.model n) ℂ) *
                (B.map n t : Matrix (B.model n) (B.model n) ℂ)ᴴ) * y n *
              ((B.map n t : Matrix (B.model n) (B.model n) ℂ) *
                (B.map n g : Matrix (B.model n) (B.model n) ℂ) *
                (B.map n t : Matrix (B.model n) (B.model n) ℂ)ᴴ)ᴴ) *
          ((B.map n t : Matrix (B.model n) (B.model n) ℂ)ᴴ)ᴴ =
        (B.map n t : Matrix (B.model n) (B.model n) ℂ)ᴴ * y n *
            (B.map n t : Matrix (B.model n) (B.model n) ℂ) -
          (B.map n g : Matrix (B.model n) (B.model n) ℂ) *
            ((B.map n t : Matrix (B.model n) (B.model n) ℂ)ᴴ * y n *
              (B.map n t : Matrix (B.model n) (B.model n) ℂ)) *
            (B.map n g : Matrix (B.model n) (B.model n) ℂ)ᴴ := by
    intro n
    set P : Matrix (B.model n) (B.model n) ℂ :=
      (B.map n t : Matrix (B.model n) (B.model n) ℂ) with hPdef
    set G : Matrix (B.model n) (B.model n) ℂ :=
      (B.map n g : Matrix (B.model n) (B.model n) ℂ)
    have hPP : Pᴴ * P = 1 := by
      rw [hPdef]
      have h := (B.map n t).2
      rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at h
      exact h
    calc
      Pᴴ * (y n - P * G * Pᴴ * y n * (P * G * Pᴴ)ᴴ) * (Pᴴ)ᴴ
          = Pᴴ * y n * P -
              Pᴴ * P * (G * (Pᴴ * y n * P) * Gᴴ) * (Pᴴ * P) := by
            simp only [Matrix.conjTranspose_mul,
              Matrix.conjTranspose_conjTranspose]
            noncomm_ring
      _ = Pᴴ * y n * P - 1 * (G * (Pᴴ * y n * P) * Gᴴ) * 1 := by
            rw [hPP]
      _ = Pᴴ * y n * P - G * (Pᴴ * y n * P) * Gᴴ := by
            rw [one_mul, mul_one]
  exact hrot.congr hid

/-- **Move 1.**  A mass-bounded sequence whose displacement against the
*compressed* generators `t iota(a) t⁻¹`, `a ∈ S`, is scaled-mass null rotates
into the scaled asymptotic commutant of the whole of `iota(Gamma)`.

Two steps: `scaledMassVanishing_rotate` at each generator, then
`CollapseTransportDiagonalizationCommutant.isScaledAsymptoticCommutantOf_of_generating`
to pass from the Kazhdan generating set to all of `Gamma`.  Checking only the
generators is what Step 6 actually does. -/
theorem isScaledAsymptoticCommutantOf_of_conj_generating (hw : ∀ n, 0 ≤ w n)
    (iota : Γ →* E) (t : E) (S : Finset Γ)
    (hgen : Subgroup.closure (S : Set Γ) = ⊤)
    (hbound : IsScaledMassBounded B w y)
    (hS : ∀ a ∈ S, ScaledMassVanishing B w (fun n ↦
      y n -
        (B.map n (t * iota a * t⁻¹) :
            Matrix (B.model n) (B.model n) ℂ) * y n *
          (B.map n (t * iota a * t⁻¹) :
            Matrix (B.model n) (B.model n) ℂ)ᴴ)) :
    IsScaledAsymptoticCommutantOf B w iota (fun n ↦
      (B.map n t : Matrix (B.model n) (B.model n) ℂ)ᴴ * y n *
        (B.map n t : Matrix (B.model n) (B.model n) ℂ)) :=
  CollapseTransportDiagonalizationCommutant.isScaledAsymptoticCommutantOf_of_generating
    B w hw iota S hgen _ (scaledMassBounded_rotate t hbound)
    (fun a ha ↦ scaledMassVanishing_rotate hw t (iota a) hbound (hS a ha))

end Rotation

/-! ## Moves 2 and 3: the transport invocation -/

/-- **Step 6 at the rank weight.**  A mass-bounded sequence whose displacement
against the *compressed* Kazhdan generators is scaled-mass null lies, after
transport, in the scaled asymptotic commutant of the whole of `iota(Gamma)`.

This is the invocation the manuscript asserts and the endpoint previously
re-derived inline: `ScaledKazhdanTransport.scaled_transport_both` at the weight
`w`, which the collapse instantiates at the rank `w_n = k_n`.  The round trip
is lossless — the forward half returns `U_t (U_t* y U_t) U_t*`, which is `y`
exactly, by `U_t U_t* = 1`. -/
theorem scaledAsymptoticCommutant_of_conj_vanishing
    {B : OpAlmostRepresentation E} {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n)
    (C : KazhdanCompressionCore Γ E) (S : Finset Γ)
    (hgen : Subgroup.closure (S : Set Γ) = ⊤)
    {y : ∀ n, Matrix (B.model n) (B.model n) ℂ}
    (hbound : IsScaledMassBounded B w y)
    (hS : ∀ a ∈ S, ScaledMassVanishing B w (fun n ↦
      y n -
        (B.map n (C.t * C.iota a * C.t⁻¹) :
            Matrix (B.model n) (B.model n) ℂ) * y n *
          (B.map n (C.t * C.iota a * C.t⁻¹) :
            Matrix (B.model n) (B.model n) ℂ)ᴴ)) :
    IsScaledAsymptoticCommutant B w C y := by
  -- Move 1: the rotated sequence commutes with the uncompressed group
  have hx : IsScaledAsymptoticCommutant B w C (fun n ↦
      (B.map n C.t : Matrix (B.model n) (B.model n) ℂ)ᴴ * y n *
        (B.map n C.t : Matrix (B.model n) (B.model n) ℂ)) :=
    isScaledAsymptoticCommutantOf_of_conj_generating hw C.iota C.t S hgen
      hbound hS
  -- Move 2: the transport theorem, at the weight `w`
  have htrans := (scaled_transport_both B w hw C _ hx
    (scaledMassBounded_rotate C.t hbound)).1
  -- Move 3: the round trip is the identity
  intro γ
  refine (htrans γ).congr fun n ↦ ?_
  -- `scaled_transport_both` concludes about a lambda, so instantiating the
  -- commutant definition at `n` leaves a beta-redex `(fun n ↦ …) n` in the
  -- goal.  `rw` matches only up to reducible defeq and so never sees the
  -- body; the redex has to be contracted before `set` and `rw` can bite.
  -- (The sibling `scaledMassVanishing_rotate` needs no such step because it
  -- discharges its congruence with a typed term, and `exact`-checking
  -- unfolds beta on its own.)
  simp only []
  set P : Matrix (B.model n) (B.model n) ℂ :=
    (B.map n C.t : Matrix (B.model n) (B.model n) ℂ) with hPdef
  have hPP : P * Pᴴ = 1 := by
    rw [hPdef]
    have h := (B.map n C.t).2
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at h
    exact h
  have hround : P * (Pᴴ * y n * P) * Pᴴ = y n := by
    calc
      P * (Pᴴ * y n * P) * Pᴴ = P * Pᴴ * y n * (P * Pᴴ) := by
        noncomm_ring
      _ = 1 * y n * 1 := by rw [hPP]
      _ = y n := by rw [one_mul, mul_one]
  rw [hround]

end CollapseScaledStepSix
end GroupApproximation
