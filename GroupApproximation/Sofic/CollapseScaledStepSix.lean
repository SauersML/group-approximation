import GroupApproximation.Sofic.CollapseTransportDiagonalization
import GroupApproximation.Sofic.ScaledKazhdanTransport

/-!
# Step 6 of the involutive collapse, by the weighted transport theorem

## What this module certifies, and what it does not

`non_mf_groups_exist.tex` makes two different assertions about Step 6 of
`thm:collapse`, and they are not the same assertion.

* **The printed Step 6** transports inside the Hilbert-space ultraproduct
  `K_\omega` of the `(M_{d_n}, \operatorname{Tr})`: the limiting cocycle is a
  coboundary `b(\gamma) = y - \pi(\gamma)y`, `(W2)` puts `y` in
  `\operatorname{Fix}\pi(sLs^{-1})`, and the *proof* of
  `thm:kazhdan-transport` supplies
  `\operatorname{Fix}\pi(sLs^{-1}) \subseteq \operatorname{Fix}\pi(L)`
  through `P`, `Q = \pi(s)P\pi(s)^{*}`, `P \le Q` and `Q = P`.
  **This development does not contain that route, and this module does not
  supply it.**  It cannot: the route needs `K_\omega` as a genuine Hilbert
  space — `NormedAddCommGroup`, `InnerProductSpace ℝ`, `CompleteSpace` — and
  `Sofic/UltraproductModelConstruction.lean` builds the ultraproduct as a
  *module*, stating in its own docstring that the inner product and the
  Hilbert-space structure are deliberately not built.  `Delorme`'s fixed-point
  theorem is in the repository and proved, with no `K_\omega` to apply it to.
* **The rank-weight assertion**, printed in the discussion after
  `thm:transport-variants`: "the collapse proof of Theorem `thm:collapse` uses
  a rank weight, which normalizes a defect at its own scale."  That is the
  assertion this module certifies, by actually invoking
  `ScaledKazhdanTransport.scaled_transport_both` at the weight `w_n = k_n`
  instead of re-deriving the transport inline.  It is audit row `R1` /
  `CO.14c`, with `CO.14` and `CO.14b`.

So the record, stated plainly: **the route the Lean travels at Step 6 is the
rank-weight transport, not the ultraproduct argument `thm:collapse` prints.**
An accurate record of that divergence is the outcome here; a silent divergence
would not be.

## The three moves

The primitive of Step 5 almost commutes with the microstates of `s\iota(\Gamma)s^{-1}`
— a *proper* subgroup of `\iota(\Gamma)`, which is the entire point of the
compression — because `(W2)` makes the displacement vanish exactly there.
Transport promotes that to `\iota(\Gamma)`:

1. `isScaledAsymptoticCommutantOf_of_conj` — the rotated sequence
   `x_n = U_s^{*} y_n U_s` lies in the scaled asymptotic commutant of `\iota`
   itself.  The displacement of `x` against `U_{\iota\gamma}` is the
   displacement of `y` against `U_s U_{\iota\gamma} U_s^{*}`, conjugated; and
   `U_s U_{\iota\gamma} U_s^{*}` differs from `U_{s\iota\gamma s^{-1}}` by an
   operator-norm null amount (`opNormVanishing_map_conj`), which
   `ScaledKazhdanTransport.scaled_conjugation_massVanishing_of_opNormVanishing`
   converts into a scaled-mass null difference at the weight.
2. `scaled_transport_both` applies to `x`.
3. `scaledAsymptoticCommutant_of_conj_vanishing` — its forward half returns
   `U_s x_n U_s^{*}`, which is `y_n` **exactly**, by unitarity.  Nothing is
   lost in the round trip, so `y` itself lies in the scaled asymptotic
   commutant of `\iota`.

The weight is never normalized by a dimension: it is carried as the parameter
`w`, and the collapse instantiates it at `w_n = k_n`, the rank normalization of
Step 3.
-/

namespace GroupApproximation
namespace CollapseScaledStepSix

open Matrix KazhdanCornerMatrices ScaledKazhdanTransport
open scoped Matrix.Norms.L2Operator

universe u

variable {Γ : Type} {E : Type u} [Group Γ] [Group E]

/-! ## The conjugation defect -/

/-- **Microstates of a conjugate are asymptotically the conjugate of the
microstates.**  `U_{tgt^{-1}}` and `U_t U_g U_t^{*}` differ by an
operator-norm null amount: three defects — the two multiplicative ones of
`t g` against `t^{-1}` and of `t` against `g`, and the inversion defect
`U_{t^{-1}} \approx U_t^{*}` — telescope. -/
theorem opNormVanishing_map_conj (B : OpAlmostRepresentation E) (t g : E) :
    OpNormVanishing B (fun n ↦
      (B.map n (t * g * t⁻¹) : Matrix (B.model n) (B.model n) ℂ) -
        (B.map n t : Matrix (B.model n) (B.model n) ℂ) *
          (B.map n g : Matrix (B.model n) (B.model n) ℂ) *
          (B.map n t : Matrix (B.model n) (B.model n) ℂ)ᴴ) := by
  have h1 := multiplicativeDefect_vanishing B (t * g) t⁻¹
  have h2 := (multiplicativeDefect_vanishing B t g).mul_right_of_norm_le_one
    (fun n ↦ (B.map n t⁻¹ : Matrix (B.model n) (B.model n) ℂ))
    (fun n ↦ norm_le_one_of_mem_unitary (B.map n t⁻¹).2)
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
          mul_le_mul (norm_le_one_of_mem_unitary (B.map n t).2)
            (norm_le_one_of_mem_unitary (B.map n g).2) (norm_nonneg _)
            zero_le_one
        _ = 1 := one_mul 1)
  exact ((h1.add h2).add h3).congr fun n ↦ by noncomm_ring

/-! ## Move 1: rotating the commutant relation back through the compressor -/

/-- **The rotated primitive lies in the scaled asymptotic commutant of the
uncompressed group.**  If the mass-bounded sequence `y` has scaled-mass null
displacement against every `U_{t\iota\gamma t^{-1}}` — which is what `(W2)`
supplies for the collapse primitive, at the compressed copy only — then
`x_n = U_t^{*} y_n U_t` has scaled-mass null displacement against every
`U_{\iota\gamma}`.

The rotation is exact: `U_t^{*}(y - AyA^{*})U_t = x - U_{\iota\gamma} x
U_{\iota\gamma}^{*}` for `A = U_t U_{\iota\gamma} U_t^{*}`, using
`U_t^{*}U_t = 1` twice.  Only the replacement of `A` by
`U_{t\iota\gamma t^{-1}}` is approximate, and that is exactly the hypothesis of
`scaled_conjugation_massVanishing_of_opNormVanishing`. -/
theorem isScaledAsymptoticCommutantOf_of_conj
    {B : OpAlmostRepresentation E} {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n)
    (iota : Γ →* E) (t : E)
    {y : ∀ n, Matrix (B.model n) (B.model n) ℂ}
    (hbound : IsScaledMassBounded B w y)
    (hy : ∀ γ : Γ, ScaledMassVanishing B w (fun n ↦
      y n -
        (B.map n (t * iota γ * t⁻¹) :
            Matrix (B.model n) (B.model n) ℂ) * y n *
          (B.map n (t * iota γ * t⁻¹) :
            Matrix (B.model n) (B.model n) ℂ)ᴴ)) :
    IsScaledAsymptoticCommutantOf B w iota (fun n ↦
      (B.map n t : Matrix (B.model n) (B.model n) ℂ)ᴴ * y n *
        (B.map n t : Matrix (B.model n) (B.model n) ℂ)) := by
  intro γ
  -- conjugate transposes of microstates are unitary
  have hstar : ∀ n : ℕ,
      ((B.map n t : Matrix (B.model n) (B.model n) ℂ)ᴴ) ∈
        Matrix.unitaryGroup (B.model n) ℂ := by
    intro n
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose]
    exact Unitary.star_mul_self_of_mem (B.map n t).2
  -- the conjugated generator microstate is unitary
  have hAmem : ∀ n : ℕ,
      (B.map n t : Matrix (B.model n) (B.model n) ℂ) *
          (B.map n (iota γ) : Matrix (B.model n) (B.model n) ℂ) *
          (B.map n t : Matrix (B.model n) (B.model n) ℂ)ᴴ ∈
        Matrix.unitaryGroup (B.model n) ℂ :=
    fun n ↦ mul_mem (mul_mem (B.map n t).2 (B.map n (iota γ)).2) (hstar n)
  -- replacing `U_{t ιγ t⁻¹}` by `U_t U_{ιγ} U_t*` costs a scaled-mass null term
  have hmix := scaled_conjugation_massVanishing_of_opNormVanishing hw
    (fun n ↦ B.map n (t * iota γ * t⁻¹))
    (fun n ↦ (⟨_, hAmem n⟩ : Matrix.unitaryGroup (B.model n) ℂ))
    y hbound (opNormVanishing_map_conj B t (iota γ))
  -- so the displacement against the conjugated microstate is null
  have hAy : ScaledMassVanishing B w (fun n ↦
      y n -
        ((B.map n t : Matrix (B.model n) (B.model n) ℂ) *
            (B.map n (iota γ) : Matrix (B.model n) (B.model n) ℂ) *
            (B.map n t : Matrix (B.model n) (B.model n) ℂ)ᴴ) * y n *
          ((B.map n t : Matrix (B.model n) (B.model n) ℂ) *
            (B.map n (iota γ) : Matrix (B.model n) (B.model n) ℂ) *
            (B.map n t : Matrix (B.model n) (B.model n) ℂ)ᴴ)ᴴ) :=
    ((hy γ).add hmix).congr fun n ↦ by abel
  have hrot := hAy.unitary_conjugate
    (fun n ↦ (⟨_, hstar n⟩ : Matrix.unitaryGroup (B.model n) ℂ))
  -- the rotation is exact: `U_t* (y - A y A*) U_t = x - U_{ιγ} x U_{ιγ}*`
  have hid : ∀ n : ℕ,
      (B.map n t : Matrix (B.model n) (B.model n) ℂ)ᴴ *
          (y n -
            ((B.map n t : Matrix (B.model n) (B.model n) ℂ) *
                (B.map n (iota γ) : Matrix (B.model n) (B.model n) ℂ) *
                (B.map n t : Matrix (B.model n) (B.model n) ℂ)ᴴ) * y n *
              ((B.map n t : Matrix (B.model n) (B.model n) ℂ) *
                (B.map n (iota γ) : Matrix (B.model n) (B.model n) ℂ) *
                (B.map n t : Matrix (B.model n) (B.model n) ℂ)ᴴ)ᴴ) *
          ((B.map n t : Matrix (B.model n) (B.model n) ℂ)ᴴ)ᴴ =
        (B.map n t : Matrix (B.model n) (B.model n) ℂ)ᴴ * y n *
            (B.map n t : Matrix (B.model n) (B.model n) ℂ) -
          (B.map n (iota γ) : Matrix (B.model n) (B.model n) ℂ) *
            ((B.map n t : Matrix (B.model n) (B.model n) ℂ)ᴴ * y n *
              (B.map n t : Matrix (B.model n) (B.model n) ℂ)) *
            (B.map n (iota γ) : Matrix (B.model n) (B.model n) ℂ)ᴴ := by
    intro n
    set P : Matrix (B.model n) (B.model n) ℂ :=
      (B.map n t : Matrix (B.model n) (B.model n) ℂ) with hPdef
    set G : Matrix (B.model n) (B.model n) ℂ :=
      (B.map n (iota γ) : Matrix (B.model n) (B.model n) ℂ) with hGdef
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

/-! ## Moves 2 and 3: the transport invocation -/

/-- **Step 6 at the rank weight.**  A mass-bounded sequence whose displacement
against the *compressed* copy `t\iota(\Gamma)t^{-1}` is scaled-mass null lies,
after transport, in the scaled asymptotic commutant of the whole of
`\iota(\Gamma)`.

This is the invocation the manuscript asserts and the endpoint previously
re-derived inline: `ScaledKazhdanTransport.scaled_transport_both` at the weight
`w`, which the collapse instantiates at the rank `w_n = k_n`.  The round trip
is lossless — the forward half returns `U_t (U_t^{*} y U_t) U_t^{*}`, which is
`y` exactly, by `U_t U_t^{*} = 1`. -/
theorem scaledAsymptoticCommutant_of_conj_vanishing
    {B : OpAlmostRepresentation E} {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n)
    (C : KazhdanCompressionCore Γ E)
    {y : ∀ n, Matrix (B.model n) (B.model n) ℂ}
    (hbound : IsScaledMassBounded B w y)
    (hy : ∀ γ : Γ, ScaledMassVanishing B w (fun n ↦
      y n -
        (B.map n (C.t * C.iota γ * C.t⁻¹) :
            Matrix (B.model n) (B.model n) ℂ) * y n *
          (B.map n (C.t * C.iota γ * C.t⁻¹) :
            Matrix (B.model n) (B.model n) ℂ)ᴴ)) :
    IsScaledAsymptoticCommutant B w C y := by
  -- conjugate transposes of microstates are unitary
  have hstar : ∀ n : ℕ,
      ((B.map n C.t : Matrix (B.model n) (B.model n) ℂ)ᴴ) ∈
        Matrix.unitaryGroup (B.model n) ℂ := by
    intro n
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose]
    exact Unitary.star_mul_self_of_mem (B.map n C.t).2
  -- Move 1: the rotated sequence commutes with the uncompressed group
  have hx : IsScaledAsymptoticCommutant B w C (fun n ↦
      (B.map n C.t : Matrix (B.model n) (B.model n) ℂ)ᴴ * y n *
        (B.map n C.t : Matrix (B.model n) (B.model n) ℂ)) :=
    isScaledAsymptoticCommutantOf_of_conj hw C.iota C.t hbound hy
  -- it is mass bounded, being a unitary conjugate of a mass-bounded sequence
  have hxb : IsScaledMassBounded B w (fun n ↦
      (B.map n C.t : Matrix (B.model n) (B.model n) ℂ)ᴴ * y n *
        (B.map n C.t : Matrix (B.model n) (B.model n) ℂ)) := by
    refine (hbound.unitary_conjugate
      (fun n ↦ ⟨(B.map n C.t : Matrix (B.model n) (B.model n) ℂ)ᴴ,
        hstar n⟩)).congr fun n ↦ ?_
    rw [Matrix.conjTranspose_conjTranspose]
  -- Move 2: the transport theorem, at the weight `w`
  have htrans := (scaled_transport_both B w hw C _ hx hxb).1
  -- Move 3: the round trip is the identity
  intro γ
  refine (htrans γ).congr fun n ↦ ?_
  set P : Matrix (B.model n) (B.model n) ℂ :=
    (B.map n C.t : Matrix (B.model n) (B.model n) ℂ) with hPdef
  have hPP : P * Pᴴ = 1 := by
    rw [hPdef]
    have h := (B.map n C.t).2
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at h
    exact h
  have hround : P * (Pᴴ * y n * P) * Pᴴ = y n := by
    calc
      P * (Pᴴ * y n * P) * Pᴴ = (P * Pᴴ) * y n * (P * Pᴴ) := by
        noncomm_ring
      _ = 1 * y n * 1 := by rw [hPP]
      _ = y n := by rw [one_mul, mul_one]
  rw [hround]

end CollapseScaledStepSix
end GroupApproximation
