import GroupApproximation.Analysis.CStarStinespringHom
import GroupApproximation.Analysis.CStarCompletelyPositiveStar

/-!
# The multiplicative-domain estimate at the Stinespring dilation

Toward proof-ledger row `RE.05` (the Lance debt).  The compression step of
Lance's theorem needs the standard multiplicative-domain estimate: if a
unital completely positive map `φ : A → B(H)` almost fixes a unitary `u` of
`A` against a unitary `U` of `B(H)` — `‖φ u − U‖ ≤ δ` — then `φ` almost
conjugates by it:

  `‖φ (u a u⋆) − U (φ a) U⋆‖ ≤ 2 √(2δ) ‖a‖`.

The proof is Stinespring's.  Write `φ c = V⋆ π(c) V` with `V` an isometry
(the unital case) and `π` a ⋆-representation, and set

  `X = π(u⋆) V`,  `Y = V U⋆`,  so that
  `φ(u a u⋆) = X⋆ π(a) X` and `U φ(a) U⋆ = Y⋆ π(a) Y`.

The defect `T = π(u⋆) V − V U⋆` satisfies, by the C⋆-identity and the
unitary relations,

  `T⋆ T = (U⋆ − φ(u⋆)) U + U⋆ (U − φ(u))`,

of norm at most `2δ`, so `‖T‖ ≤ √(2δ)`, and the difference of the two
compressions telescopes through `X − Y = T`.  Everything is stated at the
dilation the repository already owns (`CStarStinespringHom.stinespringRepHom`,
`stinespring_dilation_repHom`); nothing here re-proves any part of it.

## Manuscript status

Infrastructure for the Lance lane; certifies no manuscript step on its own.
`RE.05` remains conditional until the full compression statement lands.
-/

namespace GroupApproximation
namespace CStarExactness

open scoped InnerProductSpace

universe u w

variable {A : Type u} [CStarAlgebra A]
variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable (φ : A →ₗ[ℂ] (H →L[ℂ] H)) (hφ : IsCompletelyPositive φ)

/-- For a unital completely positive map the Stinespring intertwiner is an
isometry: `V⋆ V = 1`. -/
theorem adjoint_stinespringV_comp_stinespringV (hone : φ 1 = 1) :
    (ContinuousLinearMap.adjoint (stinespringV φ hφ)).comp
        (stinespringV φ hφ) = (1 : H →L[ℂ] H) := by
  have h := stinespring_dilation_repHom φ hφ 1
  rw [map_one, ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp,
    hone] at h
  exact h

/-- The intertwiner of a unital completely positive map is a contraction. -/
theorem norm_stinespringV_le_one [Nontrivial H] (hone : φ 1 = 1) :
    ‖stinespringV φ hφ‖ ≤ 1 := by
  have h := ContinuousLinearMap.norm_adjoint_comp_self (stinespringV φ hφ)
  rw [adjoint_stinespringV_comp_stinespringV φ hφ hone,
    ContinuousLinearMap.one_def, ContinuousLinearMap.norm_id] at h
  nlinarith [norm_nonneg (stinespringV φ hφ)]

/-- The adjoint of a dilation operator is the dilation operator of the
star. -/
theorem adjoint_stinespringRepOp (c : A) :
    ContinuousLinearMap.adjoint (stinespringRepOp φ hφ c)
      = stinespringRepOp φ hφ (star c) := by
  rw [← ContinuousLinearMap.star_eq_adjoint, ← stinespringRepHom_apply,
    ← map_star, stinespringRepHom_apply]

/-- The Stinespring representation is contractive, being a ⋆-homomorphism of
C⋆-algebras. -/
theorem norm_stinespringRepOp_le (c : A) :
    ‖stinespringRepOp φ hφ c‖ ≤ ‖c‖ :=
  NonUnitalStarAlgHom.norm_apply_le
    (stinespringRepHom φ hφ).toNonUnitalStarAlgHom c

/-- Composition of dilation operators is the dilation operator of the
product. -/
theorem stinespringRepOp_comp (c₁ c₂ : A) :
    (stinespringRepOp φ hφ c₁).comp (stinespringRepOp φ hφ c₂)
      = stinespringRepOp φ hφ (c₁ * c₂) := by
  have h := map_mul (stinespringRepHom φ hφ) c₁ c₂
  rw [stinespringRepHom_apply, stinespringRepHom_apply,
    stinespringRepHom_apply, ContinuousLinearMap.mul_def] at h
  exact h.symm

/-- A unitary of a unital C⋆-algebra has norm one. -/
theorem norm_eq_one_of_star_mul_self {A' : Type u} [CStarAlgebra A']
    [Nontrivial A'] {u : A'} (huu : star u * u = 1) : ‖u‖ = 1 := by
  have h : ‖u‖ * ‖u‖ = 1 := by
    rw [← CStarRing.norm_star_mul_self, huu, norm_one]
  nlinarith [norm_nonneg u]

/-- A unitary of `B(H)` has norm one. -/
theorem norm_eq_one_of_adjoint_comp [Nontrivial H] {U : H →L[ℂ] H}
    (hU : (ContinuousLinearMap.adjoint U).comp U = 1) : ‖U‖ = 1 := by
  have h2 := ContinuousLinearMap.norm_adjoint_comp_self U
  rw [hU, ContinuousLinearMap.one_def, ContinuousLinearMap.norm_id] at h2
  nlinarith [norm_nonneg U]

/-- **The square of the defect.**  For `T = π(u) V − V U` with `u` a unitary
of `A` and `U` a unitary of `B(H)`,

  `T⋆ T = (U⋆ − φ(u⋆)) U + U⋆ (U − φ u)`,

by the four dilation identities and the unitary relation `U⋆U = 1`. -/
theorem adjoint_defect_comp_defect (hone : φ 1 = 1)
    {u : A} (huu : star u * u = 1)
    {U : H →L[ℂ] H}
    (hU : (ContinuousLinearMap.adjoint U).comp U = 1) :
    (ContinuousLinearMap.adjoint
        ((stinespringRepOp φ hφ u).comp (stinespringV φ hφ)
          - (stinespringV φ hφ).comp U)).comp
      ((stinespringRepOp φ hφ u).comp (stinespringV φ hφ)
        - (stinespringV φ hφ).comp U)
      = ((ContinuousLinearMap.adjoint U - φ (star u)).comp U)
        + (ContinuousLinearMap.adjoint U).comp (U - φ u) := by
  have hdil : ∀ c : A, (ContinuousLinearMap.adjoint
      (stinespringV φ hφ)).comp ((stinespringRepOp φ hφ c).comp
        (stinespringV φ hφ)) = φ c := fun c ↦
    stinespring_dilation_repHom φ hφ c
  set V := stinespringV φ hφ with hV_def
  set W := ContinuousLinearMap.adjoint V with hW_def
  have hone' : W.comp V = 1 :=
    adjoint_stinespringV_comp_stinespringV φ hφ hone
  -- the adjoint of the defect
  have hTadj : ContinuousLinearMap.adjoint
      ((stinespringRepOp φ hφ u).comp V - V.comp U)
      = (W.comp (stinespringRepOp φ hφ (star u)))
        - (ContinuousLinearMap.adjoint U).comp W := by
    rw [map_sub, ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_comp, adjoint_stinespringRepOp]
  -- the four dilation identities
  have hterm1 : (W.comp (stinespringRepOp φ hφ (star u))).comp
      ((stinespringRepOp φ hφ u).comp V) = 1 := by
    have hseg : (stinespringRepOp φ hφ (star u)).comp
        ((stinespringRepOp φ hφ u).comp V)
        = (stinespringRepOp φ hφ 1).comp V := by
      rw [← ContinuousLinearMap.comp_assoc, stinespringRepOp_comp, huu]
    rw [ContinuousLinearMap.comp_assoc, hseg, hdil 1, hone]
  have hterm2 : (W.comp (stinespringRepOp φ hφ (star u))).comp
      (V.comp U) = (φ (star u)).comp U := by
    conv_rhs => rw [← hdil (star u)]
    simp only [ContinuousLinearMap.comp_assoc]
  have hterm3 : ((ContinuousLinearMap.adjoint U).comp W).comp
      ((stinespringRepOp φ hφ u).comp V)
      = (ContinuousLinearMap.adjoint U).comp (φ u) := by
    rw [ContinuousLinearMap.comp_assoc, hdil u]
  have hterm4 : ((ContinuousLinearMap.adjoint U).comp W).comp (V.comp U)
      = (ContinuousLinearMap.adjoint U).comp U := by
    have hWVU : W.comp (V.comp U) = U := by
      rw [← ContinuousLinearMap.comp_assoc, hone',
        ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp]
    rw [ContinuousLinearMap.comp_assoc, hWVU]
  rw [hTadj]
  simp only [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]
  rw [hterm1, hterm2, hterm3, hterm4, hU]
  abel

/-- **The defect operator estimate.**  If `φ` is unital completely positive,
`u` is a unitary of `A`, `U` is a unitary of `B(H)`, and `‖φ u − U‖ ≤ δ`,
then `‖π(u) V − V U‖ ≤ √(2δ)`: the C⋆-identity turns the square of the
defect into `(U⋆ − φ(u⋆)) U + U⋆ (U − φ u)`, of norm at most `2δ`. -/
theorem norm_repOp_comp_V_sub_V_comp_le [Nontrivial H] (hone : φ 1 = 1)
    {u : A} (huu : star u * u = 1)
    {U : H →L[ℂ] H}
    (hU : (ContinuousLinearMap.adjoint U).comp U = 1)
    {δ : ℝ} (hδ : ‖φ u - U‖ ≤ δ) :
    ‖(stinespringRepOp φ hφ u).comp (stinespringV φ hφ)
        - (stinespringV φ hφ).comp U‖ ≤ Real.sqrt (2 * δ) := by
  have hTT := adjoint_defect_comp_defect φ hφ hone huu hU
  -- the norm bound on the square
  have hstar : ‖ContinuousLinearMap.adjoint U - φ (star u)‖
      = ‖φ u - U‖ := by
    rw [← ContinuousLinearMap.star_eq_adjoint, hφ.map_star u, ← star_sub,
      norm_star, norm_sub_rev]
  have hUnorm : ‖U‖ = 1 := norm_eq_one_of_adjoint_comp hU
  have hUadj : ‖ContinuousLinearMap.adjoint U‖ = 1 := by
    rw [← ContinuousLinearMap.star_eq_adjoint, norm_star]
    exact hUnorm
  have hTTnorm : ‖(ContinuousLinearMap.adjoint
      ((stinespringRepOp φ hφ u).comp (stinespringV φ hφ)
        - (stinespringV φ hφ).comp U)).comp
      ((stinespringRepOp φ hφ u).comp (stinespringV φ hφ)
        - (stinespringV φ hφ).comp U)‖ ≤ 2 * δ := by
    rw [hTT]
    refine (norm_add_le _ _).trans ?_
    have h1 : ‖(ContinuousLinearMap.adjoint U - φ (star u)).comp U‖
        ≤ δ := by
      refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
      rw [hstar, hUnorm, mul_one]
      exact hδ
    have h2 : ‖(ContinuousLinearMap.adjoint U).comp (U - φ u)‖ ≤ δ := by
      refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
      rw [hUadj, one_mul, norm_sub_rev]
      exact hδ
    linarith
  -- conclude via the C⋆-identity for operators
  have hnorm2 : ‖(stinespringRepOp φ hφ u).comp (stinespringV φ hφ)
      - (stinespringV φ hφ).comp U‖
      * ‖(stinespringRepOp φ hφ u).comp (stinespringV φ hφ)
        - (stinespringV φ hφ).comp U‖ ≤ 2 * δ := by
    rw [← ContinuousLinearMap.norm_adjoint_comp_self]
    exact hTTnorm
  calc ‖(stinespringRepOp φ hφ u).comp (stinespringV φ hφ)
      - (stinespringV φ hφ).comp U‖
      = Real.sqrt (‖(stinespringRepOp φ hφ u).comp (stinespringV φ hφ)
          - (stinespringV φ hφ).comp U‖
        * ‖(stinespringRepOp φ hφ u).comp (stinespringV φ hφ)
          - (stinespringV φ hφ).comp U‖) :=
        (Real.sqrt_mul_self (ContinuousLinearMap.opNorm_nonneg _)).symm
    _ ≤ Real.sqrt (2 * δ) := Real.sqrt_le_sqrt hnorm2

/-- The compression of `π(a)` along `π(u⋆) V` is `φ(u a u⋆)`.  Proved in
inner-product form, the dilation's own style, so that no operator-level
normalization is ever handed to the kernel. -/
theorem compress_conj_left (u a : A) :
    (ContinuousLinearMap.adjoint
        ((stinespringRepOp φ hφ (star u)).comp (stinespringV φ hφ))).comp
      ((stinespringRepOp φ hφ a).comp
        ((stinespringRepOp φ hφ (star u)).comp (stinespringV φ hφ)))
      = φ (u * a * star u) := by
  refine ContinuousLinearMap.ext fun y => ?_
  refine ext_inner_left ℂ fun x => ?_
  have hcollapse : ∀ w : StinespringSpace φ hφ,
      stinespringRepOp φ hφ u (stinespringRepOp φ hφ a
        (stinespringRepOp φ hφ (star u) w))
      = stinespringRepOp φ hφ (u * a * star u) w := by
    intro w
    calc stinespringRepOp φ hφ u (stinespringRepOp φ hφ a
          (stinespringRepOp φ hφ (star u) w))
        = stinespringRepOp φ hφ u
            (((stinespringRepOp φ hφ a).comp
              (stinespringRepOp φ hφ (star u))) w) := rfl
      _ = stinespringRepOp φ hφ u
            (stinespringRepOp φ hφ (a * star u) w) := by
          rw [stinespringRepOp_comp]
      _ = ((stinespringRepOp φ hφ u).comp
            (stinespringRepOp φ hφ (a * star u))) w := rfl
      _ = stinespringRepOp φ hφ (u * (a * star u)) w := by
          rw [stinespringRepOp_comp]
      _ = stinespringRepOp φ hφ (u * a * star u) w := by
          rw [mul_assoc]
  calc ⟪x, ((ContinuousLinearMap.adjoint
        ((stinespringRepOp φ hφ (star u)).comp (stinespringV φ hφ))).comp
      ((stinespringRepOp φ hφ a).comp
        ((stinespringRepOp φ hφ (star u)).comp
          (stinespringV φ hφ)))) y⟫_ℂ
      = ⟪((stinespringRepOp φ hφ (star u)).comp (stinespringV φ hφ)) x,
          ((stinespringRepOp φ hφ a).comp
            ((stinespringRepOp φ hφ (star u)).comp
              (stinespringV φ hφ))) y⟫_ℂ := by
        rw [ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.adjoint_inner_right]
    _ = ⟪stinespringRepOp φ hφ (star u) (stinespringV φ hφ x),
          stinespringRepOp φ hφ a (stinespringRepOp φ hφ (star u)
            (stinespringV φ hφ y))⟫_ℂ := rfl
    _ = ⟪stinespringV φ hφ x,
          stinespringRepOp φ hφ u (stinespringRepOp φ hφ a
            (stinespringRepOp φ hφ (star u)
              (stinespringV φ hφ y)))⟫_ℂ := by
        rw [inner_stinespringRepOp_adjoint, star_star]
    _ = ⟪stinespringV φ hφ x,
          stinespringRepOp φ hφ (u * a * star u)
            (stinespringV φ hφ y)⟫_ℂ := by
        rw [hcollapse]
    _ = ⟪x, φ (u * a * star u) y⟫_ℂ :=
      inner_stinespringV_repOp φ hφ (u * a * star u) x y

/-- The compression of `π(a)` along `V U⋆` is `U φ(a) U⋆`, likewise in
inner-product form. -/
theorem compress_conj_right (U : H →L[ℂ] H) (a : A) :
    (ContinuousLinearMap.adjoint
        ((stinespringV φ hφ).comp (star U))).comp
      ((stinespringRepOp φ hφ a).comp
        ((stinespringV φ hφ).comp (star U)))
      = U * φ a * star U := by
  refine ContinuousLinearMap.ext fun y => ?_
  refine ext_inner_left ℂ fun x => ?_
  calc ⟪x, ((ContinuousLinearMap.adjoint
        ((stinespringV φ hφ).comp (star U))).comp
      ((stinespringRepOp φ hφ a).comp
        ((stinespringV φ hφ).comp (star U)))) y⟫_ℂ
      = ⟪((stinespringV φ hφ).comp (star U)) x,
          ((stinespringRepOp φ hφ a).comp
            ((stinespringV φ hφ).comp (star U))) y⟫_ℂ := by
        rw [ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.adjoint_inner_right]
    _ = ⟪stinespringV φ hφ (star U x),
          stinespringRepOp φ hφ a
            (stinespringV φ hφ (star U y))⟫_ℂ := rfl
    _ = ⟪star U x, φ a (star U y)⟫_ℂ :=
      inner_stinespringV_repOp φ hφ a (star U x) (star U y)
    _ = ⟪ContinuousLinearMap.adjoint U x, φ a (star U y)⟫_ℂ := by
        rw [ContinuousLinearMap.star_eq_adjoint]
    _ = ⟪x, U (φ a (star U y))⟫_ℂ :=
      ContinuousLinearMap.adjoint_inner_left U (φ a (star U y)) x
    _ = ⟪x, (U * φ a * star U) y⟫_ℂ := rfl

include hφ in
/-- **The multiplicative-domain estimate.**  A unital completely positive
map that moves a unitary `u` of `A` at most `δ` away from a unitary `U` of
`B(H)` conjugates by it up to `2√(2δ)`:

  `‖φ (u a u⋆) − U (φ a) U⋆‖ ≤ 2 √(2δ) ‖a‖`.

This is the estimate through which a completely positive approximation of
the identity almost commutes with the left regular unitaries — the analytic
heart of the compression step of Lance's theorem. -/
theorem norm_map_conj_sub_conj_map_le [Nontrivial A] [Nontrivial H]
    (hone : φ 1 = 1) {u : A}
    (_huu : star u * u = 1) (huu' : u * star u = 1)
    {U : H →L[ℂ] H}
    (hU : (ContinuousLinearMap.adjoint U).comp U = 1)
    (hU' : U.comp (ContinuousLinearMap.adjoint U) = 1)
    {δ : ℝ} (hδ : ‖φ u - U‖ ≤ δ) (a : A) :
    ‖φ (u * a * star u) - U * φ a * star U‖
      ≤ 2 * Real.sqrt (2 * δ) * ‖a‖ := by
  set V := stinespringV φ hφ with hV_def
  set X := (stinespringRepOp φ hφ (star u)).comp V with hX_def
  set Y := V.comp (star U) with hY_def
  have hXa : (ContinuousLinearMap.adjoint X).comp
      ((stinespringRepOp φ hφ a).comp X) = φ (u * a * star u) :=
    compress_conj_left φ hφ u a
  have hYa : (ContinuousLinearMap.adjoint Y).comp
      ((stinespringRepOp φ hφ a).comp Y) = U * φ a * star U :=
    compress_conj_right φ hφ U a
  -- the defect between the two intertwiners
  have hXY : ‖X - Y‖ ≤ Real.sqrt (2 * δ) := by
    have hsu : star (star u) * star u = 1 := by
      rw [star_star]
      exact huu'
    have hsU : (ContinuousLinearMap.adjoint (star U)).comp (star U)
        = 1 := by
      rw [← ContinuousLinearMap.star_eq_adjoint (A := star U), star_star,
        ContinuousLinearMap.star_eq_adjoint]
      exact hU'
    have hδs : ‖φ (star u) - star U‖ ≤ δ := by
      rw [hφ.map_star u, ← star_sub, norm_star]
      exact hδ
    exact norm_repOp_comp_V_sub_V_comp_le φ hφ hone hsu hsU hδs
  -- norms of the intertwiners
  have hnu : ‖star u‖ = 1 := by
    have h : star (star u) * star u = 1 := by
      rw [star_star]
      exact huu'
    exact norm_eq_one_of_star_mul_self h
  have hV1 : ‖V‖ ≤ 1 := norm_stinespringV_le_one φ hφ hone
  have hXnorm : ‖X‖ ≤ 1 := by
    rw [hX_def]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    have hπ := norm_stinespringRepOp_le φ hφ (star u)
    rw [hnu] at hπ
    calc ‖stinespringRepOp φ hφ (star u)‖ * ‖V‖ ≤ 1 * 1 :=
          mul_le_mul hπ hV1 (ContinuousLinearMap.opNorm_nonneg _)
            zero_le_one
      _ = 1 := one_mul 1
  have hUnorm : ‖U‖ = 1 := norm_eq_one_of_adjoint_comp hU
  have hYnorm : ‖Y‖ ≤ 1 := by
    rw [hY_def]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    rw [norm_star, hUnorm, mul_one]
    exact hV1
  have hXadjnorm : ‖ContinuousLinearMap.adjoint X‖ ≤ 1 := by
    rw [LinearIsometryEquiv.norm_map]
    exact hXnorm
  have hπa := norm_stinespringRepOp_le φ hφ a
  -- telescope
  have hsplit : φ (u * a * star u) - U * φ a * star U
      = (ContinuousLinearMap.adjoint X).comp
          ((stinespringRepOp φ hφ a).comp (X - Y))
        + (ContinuousLinearMap.adjoint (X - Y)).comp
            ((stinespringRepOp φ hφ a).comp Y) := by
    rw [← hXa, ← hYa, map_sub]
    simp only [ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp]
    abel
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  have hb1 : ‖(ContinuousLinearMap.adjoint X).comp
      ((stinespringRepOp φ hφ a).comp (X - Y))‖
      ≤ Real.sqrt (2 * δ) * ‖a‖ := by
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    refine le_trans (mul_le_mul hXadjnorm
      ((ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul hπa hXY (norm_nonneg _) (norm_nonneg _)))
      (norm_nonneg _) zero_le_one) ?_
    rw [one_mul, mul_comm ‖a‖]
  have hb2 : ‖(ContinuousLinearMap.adjoint (X - Y)).comp
      ((stinespringRepOp φ hφ a).comp Y)‖
      ≤ Real.sqrt (2 * δ) * ‖a‖ := by
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    have hadjXY : ‖ContinuousLinearMap.adjoint (X - Y)‖
        ≤ Real.sqrt (2 * δ) := by
      rw [LinearIsometryEquiv.norm_map]
      exact hXY
    have hcomp : ‖(stinespringRepOp φ hφ a).comp Y‖ ≤ ‖a‖ := by
      refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
      calc ‖stinespringRepOp φ hφ a‖ * ‖Y‖ ≤ ‖a‖ * 1 :=
            mul_le_mul hπa hYnorm (ContinuousLinearMap.opNorm_nonneg _)
              (norm_nonneg _)
        _ = ‖a‖ := mul_one _
    exact mul_le_mul hadjXY hcomp (norm_nonneg _) (Real.sqrt_nonneg _)
  linarith

end CStarExactness
end GroupApproximation
