import GroupApproximation.CharClass.BundleReindex

/-!
# Complex vector bundles in the projection model, XXIV: pushing a bundle along
an injection of index types

`reindex` moves a bundle along an *equivalence* of index types.  Comparing two
rank-one bundles whose index types have different **sizes** needs less: push
both into a common larger index by an injection, where a same-index invariance
applies.

The construction is the same conjugation, and it generalises because
`coordIncl_isometry` needs only injectivity.  So does the accompanying
`BundleIso`: the isomorphism uses `(coordIncl f)ᴴ * coordIncl f = 1` and never
the other side, which is the one that would need surjectivity.  `reindex` is the
special case, recorded by `reindex_eq_pushforward`.

`classifyOne_pushforward` is the consumer-facing half: the classifying map of the
pushforward is the original's followed by `cpEmbed (coordIncl f)`.

## Manuscript status

Machinery.  Certifies no manuscript step on its own.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass

open scoped Matrix
open GroupApproximation.STW59

namespace Bundle

section Pushforward

variable {X : Type} [TopologicalSpace X] {ι κ : Type} [Fintype ι] [Fintype κ]
variable [DecidableEq ι] [DecidableEq κ]

/-- **Pushing a bundle along an injection of index types**, by conjugation with
the coordinate inclusion. -/
def pushforward (f : ι → κ) (hf : Function.Injective f) (p : Bundle X ι) : Bundle X κ where
  toFun x := coordIncl f * p x * (coordIncl f)ᴴ
  continuous_toFun :=
    (continuous_const.matrix_mul p.continuous).matrix_mul continuous_const
  isStarProjection_toFun x := by
    rw [isStarProjection_matrix_iff]
    have hu : (coordIncl f)ᴴ * coordIncl f = (1 : Matrix ι ι ℂ) := coordIncl_isometry hf
    have hpH : (p x)ᴴ = p x := p.conjTranspose_eq x
    refine ⟨?_, ?_⟩
    · rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose, hpH]
      simp only [Matrix.mul_assoc]
    · calc coordIncl f * p x * (coordIncl f)ᴴ * (coordIncl f * p x * (coordIncl f)ᴴ)
          = coordIncl f * p x * ((coordIncl f)ᴴ * coordIncl f)
              * (p x * (coordIncl f)ᴴ) := by simp only [Matrix.mul_assoc]
        _ = coordIncl f * p x * (1 : Matrix ι ι ℂ) * (p x * (coordIncl f)ᴴ) := by rw [hu]
        _ = coordIncl f * p x * (p x * (coordIncl f)ᴴ) := by rw [Matrix.mul_one]
        _ = coordIncl f * (p x * p x) * (coordIncl f)ᴴ := by simp only [Matrix.mul_assoc]
        _ = coordIncl f * p x * (coordIncl f)ᴴ := by rw [p.mul_self]

theorem pushforward_apply (f : ι → κ) (hf : Function.Injective f) (p : Bundle X ι) (x : X) :
    pushforward f hf p x = coordIncl f * p x * (coordIncl f)ᴴ := rfl

/-- **The entries are those of `p`, relabelled along `f`.** -/
theorem pushforward_apply_entry (f : ι → κ) (hf : Function.Injective f) (p : Bundle X ι)
    (x : X) (i j : ι) : pushforward f hf p x (f i) (f j) = p x i j :=
  coordIncl_conj_apply hf (p x) i j

theorem trace_pushforward (f : ι → κ) (hf : Function.Injective f) (p : Bundle X ι) (x : X) :
    (pushforward f hf p x).trace = (p x).trace := by
  have hu : (coordIncl f)ᴴ * coordIncl f = (1 : Matrix ι ι ℂ) := coordIncl_isometry hf
  show (coordIncl f * p x * (coordIncl f)ᴴ).trace = (p x).trace
  rw [Matrix.trace_mul_comm]
  calc ((coordIncl f)ᴴ * (coordIncl f * p x)).trace
      = (((coordIncl f)ᴴ * coordIncl f) * p x).trace := by simp only [Matrix.mul_assoc]
    _ = (p x).trace := by rw [hu, Matrix.one_mul]

/-- **The pushforward is isomorphic to the original.**  Only the isometry half of
`coordIncl` is used, which is why an injection suffices. -/
def pushforwardIso (f : ι → κ) (hf : Function.Injective f) (p : Bundle X ι) :
    BundleIso p (pushforward f hf p) where
  hom x := coordIncl f * p x
  continuous_hom := continuous_const.matrix_mul p.continuous
  conjTranspose_mul x := by
    have hu : (coordIncl f)ᴴ * coordIncl f = (1 : Matrix ι ι ℂ) := coordIncl_isometry hf
    have hpH : (p x)ᴴ = p x := p.conjTranspose_eq x
    rw [Matrix.conjTranspose_mul, hpH]
    calc p x * (coordIncl f)ᴴ * (coordIncl f * p x)
        = p x * ((coordIncl f)ᴴ * coordIncl f) * p x := by simp only [Matrix.mul_assoc]
      _ = p x * (1 : Matrix ι ι ℂ) * p x := by rw [hu]
      _ = p x := by rw [Matrix.mul_one, p.mul_self]
  mul_conjTranspose x := by
    have hpH : (p x)ᴴ = p x := p.conjTranspose_eq x
    rw [Matrix.conjTranspose_mul, hpH]
    show coordIncl f * p x * (p x * (coordIncl f)ᴴ) = coordIncl f * p x * (coordIncl f)ᴴ
    calc coordIncl f * p x * (p x * (coordIncl f)ᴴ)
        = coordIncl f * (p x * p x) * (coordIncl f)ᴴ := by simp only [Matrix.mul_assoc]
      _ = coordIncl f * p x * (coordIncl f)ᴴ := by rw [p.mul_self]

/-- `reindex` is the special case of an equivalence. -/
theorem reindex_eq_pushforward (e : ι ≃ κ) (p : Bundle X ι) :
    reindex e p = pushforward (e : ι → κ) e.injective p := rfl

end Pushforward

/-! ### The classifying map of a pushforward -/

section Classify

variable {X : Type} [TopologicalSpace X] {a N : ℕ}

/-- **The classifying map of the pushforward is the original's, followed by the
coordinate embedding.**  This is what lets two rank-one bundles at different
index sizes be compared: push both into a common `ℂP^N` and apply a same-index
invariance there. -/
theorem classifyOne_pushforward (p : Bundle X (Fin (a + 1)))
    (hp : ∀ x, (p x).trace = 1) {f : Fin (a + 1) → Fin (N + 1)} (hf : Function.Injective f)
    (hq : ∀ x, (pushforward f hf p x).trace = 1) :
    classifyOne (pushforward f hf p) hq
      = (cpEmbed (coordIncl f) (coordIncl_isometry hf)).comp (classifyOne p hp) :=
  ContinuousMap.ext fun _ => Subtype.ext rfl

theorem trace_pushforward_eq_one (p : Bundle X (Fin (a + 1))) (hp : ∀ x, (p x).trace = 1)
    {f : Fin (a + 1) → Fin (N + 1)} (hf : Function.Injective f) (x : X) :
    (pushforward f hf p x).trace = 1 := by
  rw [trace_pushforward]
  exact hp x

end Classify

end Bundle

end CharClass
end GroupApproximation
