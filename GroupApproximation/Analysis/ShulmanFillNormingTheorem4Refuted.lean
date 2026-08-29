import GroupApproximation.Analysis.MFAlgebra
import GroupApproximation.Analysis.ShulmanFillNormingAsymptotic
import GroupApproximation.Analysis.ShulmanFillNormingScalarMF

/-!
# The model-first form of Theorem 4's lifting direction is false

Shulman's Theorem 4, in the direction Theorem 10 consumes, was first recorded in
this repository as a binder quantifying over the model *before* the
representation: for every `H`, every family `A` with `ι`, `hnorm`, `hone`, and
every faithful `π : B →⋆ₐ[ℂ] B(H)` of a separable MF `B`, an asymptotic lift of
`π` into `𝒟`.  `Theorem4ModelFirstStatement` below is that binder verbatim, and
`not_theorem4ModelFirst` refutes it.

The refutation is algebraic, not analytic.  Take the scalar model `A n = ℂ`,
`ι n z = z • 1`, on the very `H` that carries `π`; it is contractive, its units
are the identity so `hone` holds constantly, and its coefficients are MF.  Then
`𝒟` is a subalgebra of `lp (fun _ ↦ ℂ) ∞`, which is **commutative**, and the
`lift` field is exact — `q (φ_t b) = π b` for every `t`, not in the limit.  So

    π b * π c = q (φ_t b * φ_t c) = q (φ_t c * φ_t b) = π c * π b ,

whence `π (b * c) = π (c * b)` and, `π` being faithful, `b * c = c * b`.  The
recorded statement therefore forces **every separable MF algebra with a faithful
representation to be commutative**, which `C*_r(F₂)` and `M₂(ℂ)` refute.  That is
the content of `commute_of_theorem4ModelFirst`; `not_theorem4ModelFirst` is the
one-line corollary.

No range computation and no limit argument is needed, and nothing about matrix
models is used: the degenerate scalar model already breaks it.  The fault is the
quantifier order — with the model fixed first, `range q` is fixed before `π` is
chosen — so the repair is to make the model existential, built to fit `π`, which
is what Blackadar--Kirchberg actually give.

The refutation is unconditional.  `HasMFEmbedding ℂ` was carried as an explicit
hypothesis while the repository lacked it — its three introduction lemmas all
start from an algebra that already has the property — and it is now
`Analysis/ShulmanFillNormingScalarMF.hasMFEmbedding_complex`, so nothing here
assumes anything.
-/

namespace GroupApproximation
namespace ShulmanFill

open Filter Topology

noncomputable section

section ScalarModel

variable (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The scalar model: `ℂ` acting on `H` by multiples of the identity. -/
def scalarIota : ℂ →⋆ₙₐ[ℂ] (H →L[ℂ] H) where
  toFun z := z • (1 : H →L[ℂ] H)
  map_zero' := zero_smul ℂ _
  map_add' x y := add_smul x y _
  map_mul' x y := by
    show (x * y) • (1 : H →L[ℂ] H) = (x • (1 : H →L[ℂ] H)) * (y • 1)
    rw [smul_mul_assoc, one_mul, smul_smul]
  map_smul' r x := by
    show (r * x) • (1 : H →L[ℂ] H) = r • (x • (1 : H →L[ℂ] H))
    rw [mul_smul]
  map_star' x := by
    show (star x) • (1 : H →L[ℂ] H) = star (x • (1 : H →L[ℂ] H))
    rw [star_smul, star_one]

@[simp] theorem scalarIota_apply (z : ℂ) :
    scalarIota H z = z • (1 : H →L[ℂ] H) := rfl

/-- The scalar model is contractive. -/
theorem norm_scalarIota_le (_n : ℕ) (z : ℂ) : ‖scalarIota H z‖ ≤ ‖z‖ := by
  have h1 : ‖(1 : H →L[ℂ] H)‖ ≤ 1 := by
    rw [ContinuousLinearMap.one_def]
    exact ContinuousLinearMap.norm_id_le
  have h2 : ‖scalarIota H z‖ = ‖z‖ * ‖(1 : H →L[ℂ] H)‖ := norm_smul z _
  nlinarith [norm_nonneg z, norm_nonneg (1 : H →L[ℂ] H), h1, h2]

/-- Its units are the identity, so the `hone` clause holds constantly. -/
theorem tendsto_scalarIota_one (v : H) :
    Tendsto (fun _ : ℕ ↦ scalarIota H (1 : ℂ) v) atTop (𝓝 v) := by
  have hfun : (fun _ : ℕ ↦ scalarIota H (1 : ℂ) v) = fun _ : ℕ ↦ v := by
    funext _
    show ((1 : ℂ) • (1 : H →L[ℂ] H)) v = v
    rw [one_smul]
    exact _root_.one_apply_eq_self v
  rw [hfun]
  exact tendsto_const_nhds

end ScalarModel

/-- Bounded scalar sequences commute: the ambient product is `lp` of copies of
`ℂ`, and `ℂ` is commutative. -/
theorem mul_comm_boundedScalarSequence
    (x y : StarStrong.BoundedStarSequence (fun _ : ℕ ↦ ℂ)) : x * y = y * x := by
  -- Stated at `lp _ ∞` rather than at the abbrev: there `lp.ext` applies with
  -- no unfolding, and the product is pointwise by `rfl` so the entry equation
  -- is already the goal.  Given at the abbrev, the elaborator unfolds
  -- `BoundedStarSequence` looking for a pattern it never needs, and overruns.
  have key : (x * y : lp (fun _ : ℕ ↦ ℂ) (⊤ : ENNReal)) =
      (y * x : lp (fun _ : ℕ ↦ ℂ) (⊤ : ENNReal)) :=
    lp.ext (funext fun i ↦ mul_comm _ _)
  exact key

/-- **The model-first form of Theorem 4's lifting direction**, exactly as it was
first recorded in the headers of `Analysis/ShulmanFillNormingDoubleMF` and
`Analysis/ShulmanFillNormingConjugationLift`.  It is refuted below. -/
def Theorem4ModelFirstStatement : Prop :=
  ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {A : ℕ → Type} [∀ n, CStarAlgebra (A n)] [∀ n, Nontrivial (A n)]
    (ι : ∀ n, A n →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (hnorm : ∀ (n : ℕ) (x : A n), ‖ι n x‖ ≤ ‖x‖)
    (hone : ∀ v : H, Tendsto (fun n ↦ ι n (1 : A n) v) atTop (𝓝 v)),
      (∀ n, HasMFEmbedding (A n)) →
      ∀ (B : Type) [CStarAlgebra B] [TopologicalSpace.SeparableSpace B],
        IsMFAlgebra B →
        ∀ π : B →⋆ₐ[ℂ] (H →L[ℂ] H), Function.Injective π →
          Nonempty (StarStrongAsymptoticLift ι hnorm hone π)

/-- **What the model-first statement really says.**  It forces every separable
MF algebra with a faithful representation to be commutative, because the scalar
model makes `𝒟` commutative while the `lift` clause is exact. -/
theorem commute_of_theorem4ModelFirst (h : Theorem4ModelFirstStatement)
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {B : Type} [CStarAlgebra B] [TopologicalSpace.SeparableSpace B]
    (hB : IsMFAlgebra B) (π : B →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hπ : Function.Injective π) (b c : B) : b * c = c * b := by
  -- `ι` is a family `(n : ℕ) → A n →⋆ₙₐ[ℂ] B(H)`, so the scalar model has to be
  -- passed as `fun _ ↦ scalarIota H`, not as `scalarIota H`.  `A` is then
  -- solved from that type by pattern unification and needs no named argument —
  -- which is just as well, since naming a binder of a `def … : Prop` requires
  -- the elaborator to unfold it first.
  obtain ⟨φ⟩ := h (fun _ : ℕ ↦ scalarIota H) (norm_scalarIota_le H)
    (tendsto_scalarIota_one H) (fun _ ↦ hasMFEmbedding_complex) B hB π hπ
  have key : (⟨φ.toFun 0 b, φ.mem 0 b⟩ :
        StarStrong.starStrongSubalgebra (fun _ : ℕ ↦ scalarIota H)
          (norm_scalarIota_le H)
          (tendsto_scalarIota_one H)) * ⟨φ.toFun 0 c, φ.mem 0 c⟩ =
      ⟨φ.toFun 0 c, φ.mem 0 c⟩ * ⟨φ.toFun 0 b, φ.mem 0 b⟩ :=
    Subtype.ext (mul_comm_boundedScalarSequence _ _)
  apply hπ
  rw [map_mul, map_mul, ← φ.lift 0 b, ← φ.lift 0 c, ← map_mul, ← map_mul, key]

/-- **The model-first statement is false.**  Any non-commuting pair in any
separable MF algebra with a faithful representation refutes it; `M₂(ℂ)` and
`C*_r(F₂)` are both such. -/
theorem not_theorem4ModelFirst
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {B : Type} [CStarAlgebra B] [TopologicalSpace.SeparableSpace B]
    (hB : IsMFAlgebra B) (π : B →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hπ : Function.Injective π) {b c : B} (hbc : b * c ≠ c * b) :
    ¬ Theorem4ModelFirstStatement :=
  fun h ↦ hbc (commute_of_theorem4ModelFirst h hB π hπ b c)

end

end ShulmanFill
end GroupApproximation
