import GroupApproximation.Sofic.FinitePacketDisplacementCocycle
import GroupApproximation.Stability.MixedApproximation

/-!
# Extending generator covariance along chosen words

Exact covariance under a symmetric generating set extends to every group
element by multiplying the coordinate movers along a chosen shortest word.
No relation among the chosen mover lifts is required: only their adjoint
actions on the packet orbit matter.
-/

namespace GroupApproximation
namespace FinitePacketWordCovariance

open Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {Γ Y : Type*} [Group Γ] [Fintype Y] [DecidableEq Y]

/-- A fixed shortest word for every group element. -/
def chosenWord (S : Finset Γ)
    (hgen : WordMetric.IsSymmetricGeneratingSet (S : Set Γ))
    (g : Γ) : List Γ :=
  Classical.choose (WordMetric.exists_isWord_length_eq hgen g)

theorem chosenWord_letters (S : Finset Γ)
    (hgen : WordMetric.IsSymmetricGeneratingSet (S : Set Γ))
    (g a : Γ) (ha : a ∈ chosenWord S hgen g) : a ∈ S :=
  Finset.mem_coe.mp
    ((Classical.choose_spec
      (WordMetric.exists_isWord_length_eq hgen g)).1.letters a ha)

theorem chosenWord_prod (S : Finset Γ)
    (hgen : WordMetric.IsSymmetricGeneratingSet (S : Set Γ))
    (g : Γ) : (chosenWord S hgen g).prod = g :=
  (Classical.choose_spec (WordMetric.exists_isWord_length_eq hgen g)).1.prod_eq

/-- Multiply coordinate movers in the order of a word. -/
def wordMoverList (U : Γ → Matrix.unitaryGroup Y ℂ) :
    List Γ → Matrix.unitaryGroup Y ℂ
  | [] => 1
  | a :: l => U a * wordMoverList U l

omit [Group Γ] in
theorem wordMoverList_val_nil (U : Γ → Matrix.unitaryGroup Y ℂ) :
    (wordMoverList U [] : Matrix Y Y ℂ) = 1 := rfl

omit [Group Γ] in
theorem wordMoverList_val_cons (U : Γ → Matrix.unitaryGroup Y ℂ)
    (a : Γ) (l : List Γ) :
    (wordMoverList U (a :: l) : Matrix Y Y ℂ) =
      (U a : Matrix Y Y ℂ) * (wordMoverList U l : Matrix Y Y ℂ) := rfl

/-- Covariance propagates from letters to their ordered product. -/
theorem covariance_wordMoverList
    (V : Γ → Matrix Y Y ℂ)
    (U : Γ → Matrix.unitaryGroup Y ℂ)
    (S : Finset Γ)
    (hcov : ∀ a ∈ S, ∀ x,
      V (a * x) = (U a : Matrix Y Y ℂ) * V x *
        (U a : Matrix Y Y ℂ)ᴴ)
    (l : List Γ) (hl : ∀ a ∈ l, a ∈ S) (x : Γ) :
    V (l.prod * x) =
      (wordMoverList U l : Matrix Y Y ℂ) * V x *
        (wordMoverList U l : Matrix Y Y ℂ)ᴴ := by
  induction l with
  | nil => simp [wordMoverList]
  | cons a l ih =>
      have ha : a ∈ S := hl a List.mem_cons_self
      have htail : ∀ b ∈ l, b ∈ S :=
        fun b hb ↦ hl b (List.mem_cons_of_mem a hb)
      rw [List.prod_cons, mul_assoc, hcov a ha, ih htail]
      simp only [wordMoverList_val_cons, Matrix.conjTranspose_mul]
      noncomm_ring

/-- The coordinate mover attached to a group element by its chosen word. -/
def wordMover (S : Finset Γ)
    (hgen : WordMetric.IsSymmetricGeneratingSet (S : Set Γ))
    (U : Γ → Matrix.unitaryGroup Y ℂ) (g : Γ) :
    Matrix.unitaryGroup Y ℂ :=
  wordMoverList U (chosenWord S hgen g)

/-- Generator covariance therefore gives exact covariance for every group
element, with no compatibility equations required among the mover lifts. -/
theorem covariance_wordMover
    (V : Γ → Matrix Y Y ℂ)
    (U : Γ → Matrix.unitaryGroup Y ℂ)
    (S : Finset Γ)
    (hgen : WordMetric.IsSymmetricGeneratingSet (S : Set Γ))
    (hcov : ∀ a ∈ S, ∀ x,
      V (a * x) = (U a : Matrix Y Y ℂ) * V x *
        (U a : Matrix Y Y ℂ)ᴴ)
    (g x : Γ) :
    V (g * x) =
      (wordMover S hgen U g : Matrix Y Y ℂ) * V x *
        (wordMover S hgen U g : Matrix Y Y ℂ)ᴴ := by
  have h := covariance_wordMoverList V U S hcov (chosenWord S hgen g)
    (chosenWord_letters S hgen g) x
  simpa only [chosenWord_prod, wordMover] using h

variable {X : ℕ → FiniteModel}

/-- The coordinate word mover formed stagewise from a family of generator
movers. -/
def wordMoverFamily (S : Finset Γ)
    (hgen : WordMetric.IsSymmetricGeneratingSet (S : Set Γ))
    (U : Γ → ∀ n, Matrix.unitaryGroup (X n) ℂ) (g : Γ) :
    ∀ n, Matrix.unitaryGroup (X n) ℂ :=
  fun n ↦ wordMover S hgen (fun a ↦ U a n) g

/-- Products of coordinate mover lifts represent the corresponding product
in the norm-matrix corona. -/
theorem wordMoverList_lifts
    (rho : Γ →* NormMatrixCoronaUnitary X)
    (U : Γ → ∀ n, Matrix.unitaryGroup (X n) ℂ)
    (S : Finset Γ)
    (hU : ∀ a ∈ S,
      (QuotientGroup.mk (U a) : NormMatrixCoronaUnitary X) = rho a)
    (l : List Γ) (hl : ∀ a ∈ l, a ∈ S) :
    (QuotientGroup.mk
        (fun n ↦ wordMoverList (fun a ↦ U a n) l) :
      NormMatrixCoronaUnitary X) = rho l.prod := by
  induction l with
  | nil =>
      change QuotientGroup.mk
          (1 : ∀ n, Matrix.unitaryGroup (X n) ℂ) = rho 1
      rw [map_one]
      exact map_one (QuotientGroup.mk' (nullCofiniteOpSubgroup X))
  | cons a l ih =>
      have ha : a ∈ S := hl a List.mem_cons_self
      have htail : ∀ b ∈ l, b ∈ S :=
        fun b hb ↦ hl b (List.mem_cons_of_mem a hb)
      change QuotientGroup.mk
          (U a * fun n ↦ wordMoverList (fun b ↦ U b n) l) =
        rho (a * l.prod)
      rw [QuotientGroup.mk_mul, hU a ha, ih htail, map_mul]

/-- The chosen-word coordinate mover is a lift of the original corona
homomorphism at every group element. -/
theorem wordMoverFamily_lifts
    (rho : Γ →* NormMatrixCoronaUnitary X)
    (U : Γ → ∀ n, Matrix.unitaryGroup (X n) ℂ)
    (S : Finset Γ)
    (hgen : WordMetric.IsSymmetricGeneratingSet (S : Set Γ))
    (hU : ∀ a ∈ S,
      (QuotientGroup.mk (U a) : NormMatrixCoronaUnitary X) = rho a)
    (g : Γ) :
    (QuotientGroup.mk (wordMoverFamily S hgen U g) :
      NormMatrixCoronaUnitary X) = rho g := by
  have h := wordMoverList_lifts rho U S hU (chosenWord S hgen g)
    (chosenWord_letters S hgen g)
  change QuotientGroup.mk
      (fun n ↦ wordMoverList (fun a ↦ U a n) (chosenWord S hgen g)) = rho g
  simpa only [chosenWord_prod] using h

/-- Chosen-word movers and the ambient almost representation are
operator-norm equivalent coordinatewise, because they define the same corona
element. -/
theorem wordMoverFamily_opNormVanishing
    {E : Type} [Group E]
    (B : OpAlmostRepresentation E) (iota : Γ →* E)
    (U : Γ → ∀ n, Matrix.unitaryGroup (B.model n) ℂ)
    (S : Finset Γ)
    (hgen : WordMetric.IsSymmetricGeneratingSet (S : Set Γ))
    (hU : ∀ a ∈ S,
      (QuotientGroup.mk (U a) : NormMatrixCoronaUnitary B.model) =
        (OpAlmostRepresentation.coronaHom B) (iota a))
    (g : Γ) :
    KazhdanCornerMatrices.OpNormVanishing B (fun n ↦
      (wordMoverFamily S hgen U g n :
          Matrix (B.model n) (B.model n) ℂ) -
        (B.map n (iota g) : Matrix (B.model n) (B.model n) ℂ)) := by
  let rho : Γ →* NormMatrixCoronaUnitary B.model :=
    (OpAlmostRepresentation.coronaHom B).comp iota
  have hclass :
      (QuotientGroup.mk (wordMoverFamily S hgen U g) :
          NormMatrixCoronaUnitary B.model) =
        QuotientGroup.mk (fun n ↦ B.map n (iota g)) := by
    calc
      QuotientGroup.mk (wordMoverFamily S hgen U g) = rho g :=
        wordMoverFamily_lifts rho U S hgen hU g
      _ = (OpAlmostRepresentation.coronaHom B) (iota g) := rfl
      _ = QuotientGroup.mk (fun n ↦ B.map n (iota g)) := rfl
  have hnull :
      (wordMoverFamily S hgen U g)⁻¹ * (fun n ↦ B.map n (iota g)) ∈
        nullCofiniteOpSubgroup B.model := QuotientGroup.eq.mp hclass
  intro ε hε
  have hev := hnull ε hε
  rw [Nat.cofinite_eq_atTop, Filter.eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  refine ⟨N, fun n hn ↦ ?_⟩
  have h := hN n hn
  change opLength (B.model n)
      ((wordMoverFamily S hgen U g n)⁻¹ * B.map n (iota g)) < ε at h
  rw [opLength_inv_mul] at h
  rw [norm_sub_rev]
  exact h.le

/-- For a sequence bounded at a nonnegative rank weight, replacing a
chosen-word mover by the ambient almost-representation mover changes its
conjugate by scaled-mass zero. -/
theorem wordMoverFamily_scaled_conjugation
    {E : Type} [Group E]
    (B : OpAlmostRepresentation E) (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n)
    (iota : Γ →* E)
    (U : Γ → ∀ n, Matrix.unitaryGroup (B.model n) ℂ)
    (S : Finset Γ)
    (hgen : WordMetric.IsSymmetricGeneratingSet (S : Set Γ))
    (hU : ∀ a ∈ S,
      (QuotientGroup.mk (U a) : NormMatrixCoronaUnitary B.model) =
        (OpAlmostRepresentation.coronaHom B) (iota a))
    (x : ∀ n, Matrix (B.model n) (B.model n) ℂ)
    (hbound : ScaledKazhdanTransport.IsScaledMassBounded B w x)
    (g : Γ) :
    ScaledKazhdanTransport.ScaledMassVanishing B w (fun n ↦
      (wordMoverFamily S hgen U g n :
          Matrix (B.model n) (B.model n) ℂ) * x n *
          (wordMoverFamily S hgen U g n :
            Matrix (B.model n) (B.model n) ℂ)ᴴ -
        (B.map n (iota g) : Matrix (B.model n) (B.model n) ℂ) * x n *
          (B.map n (iota g) : Matrix (B.model n) (B.model n) ℂ)ᴴ) :=
  ScaledKazhdanTransport.scaled_conjugation_massVanishing_of_opNormVanishing
    hw (wordMoverFamily S hgen U g) (fun n ↦ B.map n (iota g)) x hbound
    (wordMoverFamily_opNormVanishing B iota U S hgen hU g)

end

end FinitePacketWordCovariance
end GroupApproximation
