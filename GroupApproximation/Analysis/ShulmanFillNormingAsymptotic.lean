import GroupApproximation.Analysis.StarStrongMatrixSequencesShulman

/-!
# Discrete asymptotic homomorphisms into `𝒟`

`Analysis/ShulmanFillNormingResiduallyFinite` shows that Shulman's Theorem 4
cannot be read with a `*`-homomorphic lift `B →⋆ₐ[ℂ] 𝒟`: coordinate evaluation
would make `B` residually finite-dimensional, and MF algebras need not be.
Theorem 4 is stated with a **discrete asymptotic homomorphism**, and this
module supplies that vocabulary.

`StarStrongAsymptoticLift ι hnorm hone π` is a sequence of maps
`φ_t : B → ∏ₙ A n` whose values lie in `𝒟`, which are contractive, whose
linearity, multiplicativity and adjoint defects vanish as `t → ∞`, and each of
which lifts the given representation exactly: `q (φ_t b) = π b`.  Nothing is
asymptotic about the lifting clause — only about the algebra.

The coordinate argument that refutes the `*`-homomorphic reading does not apply
here, and cannot: `φ_t` composed with a coordinate is not a homomorphism, only
an asymptotically multiplicative map, so no finite-dimensional representation
of `B` is produced.

## What is proved here

* `StarStrongAsymptoticLift.ofStarAlgHom` — the vocabulary is not empty: a
  `*`-homomorphic lift is one, with all four defects identically zero.  So the
  new notion is weaker than the refuted one, as it must be.
* `StarStrongAsymptoticLift.norm_apply_eq` — **every member of such a family is
  isometric.**  `q` is contractive (`StarStrong.norm_starStrongLimit_le`) and
  `q (φ_t b) = π b`, so `‖b‖ = ‖π b‖ = ‖q (φ_t b)‖ ≤ ‖φ_t b‖ ≤ ‖b‖`.  This is
  where faithfulness of the limit enters, and it enters exactly.
* `StarStrongAsymptoticLift.eventually_norm_coord_gt` — the quantitative form:
  for `c < ‖b‖` the coordinates `‖(φ_t b) n‖` are eventually above `c`.  This
  is the contrapositive of `StarStrong.norm_starStrongLimit_le_of_frequently`,
  and it is what lets a single coordinate be selected without losing the norm.

`Analysis/ShulmanFillNormingAsymptoticMF` consumes the last two and concludes
that `B` is MF — the direction Shulman's Theorem 10 ends with, in the
vocabulary Theorem 4 is actually stated in.

## If the construction only lifts asymptotically

`lift` asks for `q (φ_t b) = π b` at every `t`, which is what "lifts" means in
the printed statement.  Should the construction that eventually discharges
Theorem 4 produce only `q ∘ φ_t → π` pointwise, the two consequences above
survive in asymptotic form and nothing downstream changes: `*`-strong
convergence is enough for `‖π b‖ ≤ liminf ‖q (φ_t b)‖ ≤ liminf ‖φ_t b‖`, so
the maps are asymptotically isometric, and the coordinate bound is then
available for all large `t` — which is all
`Analysis/ShulmanFillNormingAsymptoticMF` uses, since its stage index runs to
infinity anyway.  Weakening the field is a local edit to this file and to the
two lemmas below.
-/

namespace GroupApproximation
namespace ShulmanFill

open Filter Topology

noncomputable section

universe u v

section Asymptotic

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H]
variable {A : ℕ → Type u} [∀ n, CStarAlgebra (A n)]
-- `lp _ ∞` is a unital ring only when its factors are, so the `𝒟` API now
-- carries this; `StarStrongLimitNorm` declares it the same way.
variable [∀ n, Nontrivial (A n)]
variable (ι : ∀ n, A n →⋆ₙₐ[ℂ] (H →L[ℂ] H))
variable (hnorm : ∀ (n : ℕ) (x : A n), ‖ι n x‖ ≤ ‖x‖)
variable (hone : ∀ v : H, Tendsto (fun n ↦ ι n (1 : A n) v) atTop (𝓝 v))
variable {B : Type v} [CStarAlgebra B]

/-- **A discrete asymptotic homomorphism into `𝒟` lifting `π`.**  This is the
shape Shulman's Theorem 4 is stated in: a sequence of contractive maps
`φ_t : B → ∏ₙ A n` taking values in `𝒟`, asymptotically linear,
multiplicative and adjoint-preserving, each of which the `*`-strong limit map
`q` carries back to the given representation `π`.

The values are recorded in the bounded product with membership in `𝒟` as a
separate clause, so that all four defects are measured in the product norm,
which is the norm of `𝒟`. -/
structure StarStrongAsymptoticLift (π : B →⋆ₐ[ℂ] (H →L[ℂ] H)) where
  /-- The maps of the family. -/
  toFun : ℕ → B → StarStrong.BoundedStarSequence A
  /-- Every value converges `*`-strongly, that is, lies in `𝒟`. -/
  mem : ∀ t b, toFun t b ∈ StarStrong.starStrongSubalgebra ι hnorm hone
  /-- The maps are contractive. -/
  norm_le : ∀ t b, ‖toFun t b‖ ≤ ‖b‖
  /-- The additivity defect vanishes. -/
  tendsto_add : ∀ b c, Tendsto
    (fun t ↦ ‖toFun t (b + c) - toFun t b - toFun t c‖) atTop (𝓝 0)
  /-- The homogeneity defect vanishes. -/
  tendsto_smul : ∀ (z : ℂ) (b : B), Tendsto
    (fun t ↦ ‖toFun t (z • b) - z • toFun t b‖) atTop (𝓝 0)
  /-- The multiplicativity defect vanishes. -/
  tendsto_mul : ∀ b c, Tendsto
    (fun t ↦ ‖toFun t (b * c) - toFun t b * toFun t c‖) atTop (𝓝 0)
  /-- The adjoint defect vanishes. -/
  tendsto_star : ∀ b, Tendsto
    (fun t ↦ ‖toFun t (star b) - star (toFun t b)‖) atTop (𝓝 0)
  /-- The unitality defect vanishes.  Shulman's lifts are unital, and this is
  what makes the glued map on an amalgam unital rather than merely
  non-unital. -/
  tendsto_one : Tendsto (fun t ↦ ‖toFun t (1 : B) - 1‖) atTop (𝓝 0)
  /-- Each member lifts `π` through the `*`-strong limit map. -/
  lift : ∀ t b, StarStrong.starStrongLimitHom ι hnorm hone
    ⟨toFun t b, mem t b⟩ = π b

namespace StarStrongAsymptoticLift

/-- **The vocabulary is not empty, and it is weaker than the refuted one.**  A
`*`-homomorphic lift is a discrete asymptotic homomorphism whose four defects
are identically zero.  So anything proved from the asymptotic notion applies to
the `*`-homomorphic one, and the converse fails by
`Analysis/ShulmanFillNormingResiduallyFinite`. -/
def ofStarAlgHom (π : B →⋆ₐ[ℂ] (H →L[ℂ] H))
    (rho : B →⋆ₐ[ℂ] StarStrong.starStrongSubalgebra ι hnorm hone)
    (hrho : ∀ b : B,
      StarStrong.starStrongLimitHom ι hnorm hone (rho b) = π b) :
    StarStrongAsymptoticLift ι hnorm hone π :=
  let f : B →⋆ₐ[ℂ] StarStrong.BoundedStarSequence A :=
    ((StarStrong.starStrongSubalgebra ι hnorm hone).subtype).comp rho
  { toFun := fun _ b ↦ f b
    mem := fun _ b ↦ (rho b).2
    norm_le := fun _ b ↦ NonUnitalStarAlgHom.norm_apply_le f b
    tendsto_add := fun b c ↦ by
      have h : (fun _ : ℕ ↦ ‖f (b + c) - f b - f c‖) = fun _ : ℕ ↦ (0 : ℝ) := by
        funext _
        rw [map_add]
        simp
      rw [h]
      exact tendsto_const_nhds
    tendsto_smul := fun z b ↦ by
      have h : (fun _ : ℕ ↦ ‖f (z • b) - z • f b‖) = fun _ : ℕ ↦ (0 : ℝ) := by
        funext _
        rw [map_smul]
        simp
      rw [h]
      exact tendsto_const_nhds
    tendsto_mul := fun b c ↦ by
      have h : (fun _ : ℕ ↦ ‖f (b * c) - f b * f c‖) = fun _ : ℕ ↦ (0 : ℝ) := by
        funext _
        rw [map_mul]
        simp
      rw [h]
      exact tendsto_const_nhds
    tendsto_star := fun b ↦ by
      have h : (fun _ : ℕ ↦ ‖f (star b) - star (f b)‖) = fun _ : ℕ ↦ (0 : ℝ) := by
        funext _
        rw [map_star]
        simp
      rw [h]
      exact tendsto_const_nhds
    tendsto_one := by
      have h : (fun _ : ℕ ↦ ‖f (1 : B) - 1‖) = fun _ : ℕ ↦ (0 : ℝ) := by
        funext _
        rw [map_one]
        simp
      rw [h]
      exact tendsto_const_nhds
    lift := fun _ b ↦ hrho b }

variable {ι hnorm hone}
variable {π : B →⋆ₐ[ℂ] (H →L[ℂ] H)}

/-- The `*`-strong limit of a member, as an operator on `H`. -/
theorem starStrongLimit_toFun (φ : StarStrongAsymptoticLift ι hnorm hone π)
    (t : ℕ) (b : B) :
    StarStrong.starStrongLimit ι hnorm hone ⟨φ.toFun t b, φ.mem t b⟩ = π b :=
  φ.lift t b

/-- **Every member of a lifting family is isometric.**  `q` is contractive and
carries `φ_t b` to `π b`, and `π` is isometric because it is an injective
`*`-homomorphism of C-star algebras, so the contraction `φ_t` cannot lose any
norm. -/
theorem norm_apply_eq (φ : StarStrongAsymptoticLift ι hnorm hone π)
    (hπ : Function.Injective π) (t : ℕ) (b : B) : ‖φ.toFun t b‖ = ‖b‖ := by
  have hiso : Isometry π :=
    NonUnitalStarAlgHom.isometry π.toNonUnitalStarAlgHom hπ
  have hπnorm : ‖π b‖ = ‖b‖ := hiso.norm_map_of_map_zero (map_zero _) b
  have hq : ‖StarStrong.starStrongLimit ι hnorm hone
      ⟨φ.toFun t b, φ.mem t b⟩‖ ≤ ‖φ.toFun t b‖ :=
    StarStrong.norm_starStrongLimit_le ι hnorm hone ⟨φ.toFun t b, φ.mem t b⟩
  rw [starStrongLimit_toFun φ t b, hπnorm] at hq
  exact le_antisymm (φ.norm_le t b) hq

/-- **The quantitative form: no coordinate may drop the norm in the limit.**
If `c < ‖b‖` then all but finitely many coordinates of `φ_t b` have norm above
`c`.  This is the contrapositive of
`StarStrong.norm_starStrongLimit_le_of_frequently`: a bound holding infinitely
often would bound the `*`-strong limit, which is `π b` and has norm `‖b‖`. -/
theorem eventually_norm_coord_gt (φ : StarStrongAsymptoticLift ι hnorm hone π)
    (hπ : Function.Injective π) (t : ℕ) (b : B) {c : ℝ} (hc : 0 ≤ c)
    (hcb : c < ‖b‖) :
    ∀ᶠ n in atTop, c < ‖φ.toFun t b n‖ := by
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  have hfreq : ∃ᶠ n in atTop, ‖φ.toFun t b n‖ ≤ c :=
    hcon.mono fun _ hn ↦ not_lt.mp hn
  have hle : ‖StarStrong.starStrongLimit ι hnorm hone
      ⟨φ.toFun t b, φ.mem t b⟩‖ ≤ c :=
    StarStrong.norm_starStrongLimit_le_of_frequently ι hnorm hone
      ⟨φ.toFun t b, φ.mem t b⟩ hc hfreq
  rw [starStrongLimit_toFun φ t b] at hle
  have hiso : Isometry π :=
    NonUnitalStarAlgHom.isometry π.toNonUnitalStarAlgHom hπ
  have hπnorm : ‖π b‖ = ‖b‖ := hiso.norm_map_of_map_zero (map_zero _) b
  rw [hπnorm] at hle
  exact absurd hcb (not_lt.mpr hle)

/-- Each coordinate of each member is contractive: an `ℓ∞`-coordinate is
bounded by the norm of the sequence. -/
theorem norm_coord_le (φ : StarStrongAsymptoticLift ι hnorm hone π)
    (t : ℕ) (b : B) (n : ℕ) : ‖φ.toFun t b n‖ ≤ ‖b‖ :=
  (lp.norm_apply_le_norm ENNReal.top_ne_zero (φ.toFun t b) n).trans
    (φ.norm_le t b)

end StarStrongAsymptoticLift

end Asymptotic

end

end ShulmanFill
end GroupApproximation
