import GroupApproximation.Sofic.TensorPowerAmplification
import GroupApproximation.Sofic.IntertwinerKazhdanTransport

/-!
# Tensor powers of operator-norm almost representations

`Sofic.IntertwinerKazhdanTransport` transports asymptotic intertwiners
between *any* two operator-norm almost representations of the ambient
group, and its header names the fixed-tensor instance `B₁ = U^{⊗p}`,
`B₂ = U^{⊗q}` as the intended application.  This file builds that
instance.  (The manuscript's fixed-tensor sentence was an instantiation of
this theorem until 2026-08-18, when the paragraph was cut together with the
intertwiner clause of `thm:transport-variants`; the mathematics stands on its
own.)

The analytic input is already available: `l2_opNorm_opTensorPow_sub_le`
telescopes the `p`-fold Kronecker power of unitaries, so the power moves
by at most `p` times the original operator-norm distance.  Kronecker
powers are exactly multiplicative (`opTensorPow_mul`) and preserve
unitarity (`opTensorPow_mem_unitaryGroup`), so the `p`-th tensor power of
an operator-norm almost representation is again one: the multiplicative
defect is merely multiplied by `p`, which an asymptotic hypothesis
absorbs by shrinking the input tolerance.

Fixed tensors of type `(p, q)` are the rectangular intertwiners between
two such powers, and the transport theorem then applies verbatim at every
weight: one-sided compression of a Kazhdan image creates no asymptotic
invariant tensors of any fixed type.
-/

namespace GroupApproximation

open Matrix
open scoped Kronecker Matrix.Norms.L2Operator

universe u

/-- Every iterated Kronecker index over a nonempty type is nonempty.  The
tensor-power model must stay a legitimate finite model, so the almost
representation's dimension hypothesis has to survive the power. -/
theorem opTensorIndex_nonempty {Y : Type} (hY : Nonempty Y) :
    ∀ n : ℕ, Nonempty (OpTensorIndex Y n)
  | 0 => ⟨PUnit.unit⟩
  | n + 1 => ⟨(hY.some, (opTensorIndex_nonempty hY n).some)⟩

namespace OpAlmostRepresentation

variable {G : Type u} [Group G]

/-- **The `p`-th tensor power of an operator-norm almost representation.**
Each model is replaced by its `p`-fold Kronecker index and each unitary by
its `p`-fold Kronecker power.  Multiplicativity is exact, so the whole
content is the defect estimate: the power of the defect is at most `p`
times the defect, which is asymptotically negligible for fixed `p`. -/
noncomputable def tensorPow (A : OpAlmostRepresentation G) (p : ℕ) :
    OpAlmostRepresentation G where
  model n := opTensorModel (A.model n) p
  modelNonempty n := by
    have hne : Nonempty (A.model n) := Fintype.card_pos_iff.mp (A.modelNonempty n)
    exact Fintype.card_pos_iff.mpr (opTensorIndex_nonempty hne p)
  map n g :=
    ⟨opTensorPow ((A.map n g : Matrix (A.model n) (A.model n) ℂ)) p,
      opTensorPow_mem_unitaryGroup (A.map n g).property p⟩
  asymptoticallyMultiplicative g h ε hε := by
    have hp1 : (0 : ℝ) < (p : ℝ) + 1 := by positivity
    obtain ⟨N, hN⟩ :=
      A.asymptoticallyMultiplicative g h (ε / ((p : ℝ) + 1)) (by positivity)
    refine ⟨N, fun n hn ↦ ?_⟩
    have hne : Nonempty (A.model n) := Fintype.card_pos_iff.mp (A.modelNonempty n)
    have hprod :
        ((A.map n g : Matrix (A.model n) (A.model n) ℂ) *
            (A.map n h : Matrix (A.model n) (A.model n) ℂ)) ∈
          Matrix.unitaryGroup (A.model n) ℂ :=
      mul_mem (A.map n g).property (A.map n h).property
    have hmul :
        opTensorPow ((A.map n g : Matrix (A.model n) (A.model n) ℂ) *
            (A.map n h : Matrix (A.model n) (A.model n) ℂ)) p =
          opTensorPow ((A.map n g : Matrix (A.model n) (A.model n) ℂ)) p *
            opTensorPow ((A.map n h : Matrix (A.model n) (A.model n) ℂ)) p :=
      opTensorPow_mul _ _ p
    have hstep :
        ‖opTensorPow ((A.map n (g * h) : Matrix (A.model n) (A.model n) ℂ)) p -
            opTensorPow ((A.map n g : Matrix (A.model n) (A.model n) ℂ) *
              (A.map n h : Matrix (A.model n) (A.model n) ℂ)) p‖ ≤
          (p : ℝ) *
            ‖(A.map n (g * h) : Matrix (A.model n) (A.model n) ℂ) -
              (A.map n g : Matrix (A.model n) (A.model n) ℂ) *
                (A.map n h : Matrix (A.model n) (A.model n) ℂ)‖ :=
      l2_opNorm_opTensorPow_sub_le hne (A.map n (g * h)).property hprod p
    show
      ‖opTensorPow ((A.map n (g * h) : Matrix (A.model n) (A.model n) ℂ)) p -
          opTensorPow ((A.map n g : Matrix (A.model n) (A.model n) ℂ)) p *
            opTensorPow ((A.map n h : Matrix (A.model n) (A.model n) ℂ)) p‖ ≤ ε
    rw [← hmul]
    refine hstep.trans ?_
    have hfrac : (p : ℝ) / ((p : ℝ) + 1) ≤ 1 := by
      rw [div_le_one hp1]; linarith
    calc
      (p : ℝ) *
          ‖(A.map n (g * h) : Matrix (A.model n) (A.model n) ℂ) -
            (A.map n g : Matrix (A.model n) (A.model n) ℂ) *
              (A.map n h : Matrix (A.model n) (A.model n) ℂ)‖
          ≤ (p : ℝ) * (ε / ((p : ℝ) + 1)) := by
            gcongr
            exact hN n hn
      _ = ((p : ℝ) / ((p : ℝ) + 1)) * ε := by ring
      _ ≤ 1 * ε := mul_le_mul_of_nonneg_right hfrac hε.le
      _ = ε := one_mul ε

@[simp] theorem tensorPow_model (A : OpAlmostRepresentation G) (p n : ℕ) :
    (A.tensorPow p).model n = opTensorModel (A.model n) p := rfl

@[simp] theorem tensorPow_map_coe (A : OpAlmostRepresentation G) (p n : ℕ)
    (g : G) :
    ((A.tensorPow p).map n g :
        Matrix ((A.tensorPow p).model n) ((A.tensorPow p).model n) ℂ) =
      opTensorPow ((A.map n g : Matrix (A.model n) (A.model n) ℂ)) p := rfl

/-- The zeroth tensor power is the one-point trivial family. -/
@[simp] theorem tensorPow_zero_map_coe (A : OpAlmostRepresentation G) (n : ℕ)
    (g : G) :
    ((A.tensorPow 0).map n g :
        Matrix ((A.tensorPow 0).model n) ((A.tensorPow 0).model n) ℂ) =
      1 := rfl

/-- The first tensor power reproduces the original unitary up to the
one-point padding of the recursive index. -/
@[simp] theorem tensorPow_one_map_coe (A : OpAlmostRepresentation G) (n : ℕ) (g : G) :
    ((A.tensorPow 1).map n g :
        Matrix ((A.tensorPow 1).model n) ((A.tensorPow 1).model n) ℂ) =
      (A.map n g : Matrix (A.model n) (A.model n) ℂ) ⊗ₖ 1 := rfl

end OpAlmostRepresentation

namespace TensorPowerTransport

open IntertwinerKazhdanTransport

/-! The ambient group is quantified at an arbitrary universe, as in the
manuscript.  See `Sofic.KazhdanAsymptoticCommutant` for why the Kazhdan source
`Γ` stays in `Type 0`. -/
variable {Γ : Type} {E : Type u} [Group Γ] [Group E]

/-- **Fixed tensors of type `(p, q)` transport.**  A fixed tensor of type
`(p, q)` is a Hilbert--Schmidt intertwiner from the `q`-th to the `p`-th
tensor power, and both powers are operator-norm almost representations of
the ambient group.  The one-sided compressor of a Kazhdan datum therefore
carries every weighted asymptotic intertwiner of any fixed type to another
one: compression creates no asymptotic invariant tensors of that type, at
any weight. -/
theorem tensorPow_scaled_intertwiner_transport
    (A : OpAlmostRepresentation E) (p q : ℕ) (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n)
    (C : KazhdanCompressionCore Γ E)
    (x : ∀ n, Matrix ((A.tensorPow p).model n) ((A.tensorPow q).model n) ℂ)
    (hx : IsScaledAsymptoticIntertwinerOf (A.tensorPow p) (A.tensorPow q) w
      C.iota x)
    (hbound : IsScaledRectMassBounded (A.tensorPow p) (A.tensorPow q) w x) :
    IsScaledAsymptoticIntertwinerOf (A.tensorPow p) (A.tensorPow q) w C.iota
      (fun n ↦
        ((A.tensorPow p).map n C.t :
            Matrix ((A.tensorPow p).model n) ((A.tensorPow p).model n) ℂ) *
          x n *
          ((A.tensorPow q).map n C.t :
            Matrix ((A.tensorPow q).model n)
              ((A.tensorPow q).model n) ℂ)ᴴ) :=
  scaled_intertwiner_transport _ _ w hw C x hx hbound

/-- The unweighted fixed-tensor statement: at weight `1` the scaled
transport is the plain one. -/
theorem tensorPow_intertwiner_transport
    (A : OpAlmostRepresentation E) (p q : ℕ)
    (C : KazhdanCompressionCore Γ E)
    (x : ∀ n, Matrix ((A.tensorPow p).model n) ((A.tensorPow q).model n) ℂ)
    (hx : IsScaledAsymptoticIntertwinerOf (A.tensorPow p) (A.tensorPow q)
      (fun _ ↦ (1 : ℝ)) C.iota x)
    (hbound : IsScaledRectMassBounded (A.tensorPow p) (A.tensorPow q)
      (fun _ ↦ (1 : ℝ)) x) :
    IsScaledAsymptoticIntertwinerOf (A.tensorPow p) (A.tensorPow q)
      (fun _ ↦ (1 : ℝ)) C.iota
      (fun n ↦
        ((A.tensorPow p).map n C.t :
            Matrix ((A.tensorPow p).model n) ((A.tensorPow p).model n) ℂ) *
          x n *
          ((A.tensorPow q).map n C.t :
            Matrix ((A.tensorPow q).model n)
              ((A.tensorPow q).model n) ℂ)ᴴ) :=
  tensorPow_scaled_intertwiner_transport A p q _ (fun _ ↦ zero_le_one) C x hx
    hbound

/-- Closed form of the fixed-tensor transport statement: nothing to the
left of the colon, every hypothesis a quantified antecedent of the printed
sentence. -/
theorem manuscriptFixedTensorTransport :
    ∀ {Γ : Type} {E : Type u} [Group Γ] [Group E]
      (A : OpAlmostRepresentation E)
      (p q : ℕ) (w : ℕ → ℝ), (∀ n, 0 ≤ w n) →
      ∀ (C : KazhdanCompressionCore Γ E)
        (x : ∀ n, Matrix ((A.tensorPow p).model n)
          ((A.tensorPow q).model n) ℂ),
        IsScaledAsymptoticIntertwinerOf (A.tensorPow p) (A.tensorPow q) w
            C.iota x →
          IsScaledRectMassBounded (A.tensorPow p) (A.tensorPow q) w x →
          IsScaledAsymptoticIntertwinerOf (A.tensorPow p) (A.tensorPow q) w
            C.iota
            (fun n ↦
              ((A.tensorPow p).map n C.t :
                  Matrix ((A.tensorPow p).model n)
                    ((A.tensorPow p).model n) ℂ) *
                x n *
                ((A.tensorPow q).map n C.t :
                  Matrix ((A.tensorPow q).model n)
                    ((A.tensorPow q).model n) ℂ)ᴴ) := by
  intro Γ E _ _ A p q w hw C x hx hbound
  exact tensorPow_scaled_intertwiner_transport A p q w hw C x hx hbound

end TensorPowerTransport
end GroupApproximation
