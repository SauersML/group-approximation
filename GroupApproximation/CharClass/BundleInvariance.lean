import GroupApproximation.CharClass.BundleSpace

/-!
# Complex vector bundles in the projection model, VI: isomorphism invariance

An isomorphism `e : BundleIso p q` -- a continuous family of partial isometries
`a x` with `a xᴴ a x = p x`, `a x a xᴴ = q x` -- carries every space attached to
`p` to the corresponding space attached to `q`, **over the base**:

* `E(p) ≅ E(q)` by `(x, v) ↦ (x, a x · v)`;
* `P(p) ≅ P(q)` by `(x, r) ↦ (x, a x · r · a xᴴ)`.

The second one needs **no normalization**: `a x` is isometric on the fibre of
`p x`, so `a r aᴴ` already has trace one.  The tautological lines correspond
under it, implemented by `a x · r` -- again with no normalization, and again by
the same computation.

## The associativity idiom

Rectangular matrices form no ring, so `noncomm_ring` is unavailable and every
reassociation is by hand.  The idiom used throughout is: state the next `calc`
step in the association that exposes the pattern to be rewritten, and discharge
the reassociation with `simp only [Matrix.mul_assoc]`, which normalizes both
sides to the same right-associated form.

## Manuscript status

Machinery.  Certifies no manuscript step on its own.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass

open scoped Matrix
open GroupApproximation.STW59

namespace Bundle

section Invariance

variable {X : Type} [TopologicalSpace X] {ι κ : Type} [Fintype ι] [Fintype κ]

/-- A point of `P(p)` absorbs `p` on the right too. -/
theorem absorb_right_of_mem_projSet {p : Bundle X ι} {z : X × Matrix ι ι ℂ}
    (hz : z ∈ projSet p) : z.2 * p z.1 = z.2 := by
  have h := congrArg Matrix.conjTranspose (absorb_of_mem_projSet hz)
  rwa [Matrix.conjTranspose_mul, p.conjTranspose_eq, hz.1] at h

/-- **Conjugating a point of `P(p)` by a partial isometry.**  The hypotheses are
exactly what an isomorphism supplies at one point of the base; stating them
separately lets the same lemma serve both directions of the homeomorphism. -/
theorem conj_mem_projSet {p : Bundle X ι} {q : Bundle X κ} {x : X} {a : Matrix κ ι ℂ}
    (haa : aᴴ * a = p x) (hqa : q x * a = a) {r : Matrix ι ι ℂ}
    (hz : ((x, r) : X × Matrix ι ι ℂ) ∈ projSet p) :
    ((x, a * r * aᴴ) : X × Matrix κ κ ℂ) ∈ projSet q := by
  have hrH : rᴴ = r := hz.1
  have hrr : r * r = r := hz.2.1
  have hpr : p x * r = r := hz.2.2.2
  have hrp : r * p x = r := absorb_right_of_mem_projSet hz
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hrH,
      Matrix.mul_assoc]
  · calc a * r * aᴴ * (a * r * aᴴ) = a * (r * ((aᴴ * a) * (r * aᴴ))) := by
          simp only [Matrix.mul_assoc]
      _ = a * (r * (p x * (r * aᴴ))) := by rw [haa]
      _ = a * ((r * p x) * (r * aᴴ)) := by simp only [Matrix.mul_assoc]
      _ = a * (r * (r * aᴴ)) := by rw [hrp]
      _ = a * ((r * r) * aᴴ) := by simp only [Matrix.mul_assoc]
      _ = a * (r * aᴴ) := by rw [hrr]
      _ = a * r * aᴴ := by simp only [Matrix.mul_assoc]
  · rw [Matrix.trace_mul_comm]
    calc (aᴴ * (a * r)).trace = ((aᴴ * a) * r).trace := by simp only [Matrix.mul_assoc]
      _ = (p x * r).trace := by rw [haa]
      _ = r.trace := by rw [hpr]
      _ = 1 := hz.2.2.1
  · calc q x * (a * r * aᴴ) = (q x * a) * r * aᴴ := by simp only [Matrix.mul_assoc]
      _ = a * r * aᴴ := by rw [hqa]

/-- The conjugation is undone by the adjoint. -/
theorem conj_conj {p : Bundle X ι} {x : X} {a : Matrix κ ι ℂ} (haa : aᴴ * a = p x)
    {r : Matrix ι ι ℂ} (hz : ((x, r) : X × Matrix ι ι ℂ) ∈ projSet p) :
    aᴴ * (a * r * aᴴ) * (aᴴ)ᴴ = r := by
  have hpr : p x * r = r := hz.2.2.2
  have hrp : r * p x = r := absorb_right_of_mem_projSet hz
  rw [Matrix.conjTranspose_conjTranspose]
  calc aᴴ * (a * r * aᴴ) * a = (aᴴ * a) * (r * (aᴴ * a)) := by simp only [Matrix.mul_assoc]
    _ = p x * (r * p x) := by rw [haa]
    _ = p x * r := by rw [hrp]
    _ = r := hpr

namespace BundleIso

variable {p : Bundle X ι} {q : Bundle X κ}

/-- The adjoint implementer is absorbed by the source projection on the left. -/
theorem conjTranspose_absorb_left (e : BundleIso p q) (x : X) :
    p x * (e.hom x)ᴴ = (e.hom x)ᴴ := by
  have h := congrArg Matrix.conjTranspose (e.hom_mul_right x)
  rwa [Matrix.conjTranspose_mul, p.conjTranspose_eq] at h

theorem conjTranspose_mul_conjTranspose (e : BundleIso p q) (x : X) :
    ((e.hom x)ᴴ)ᴴ * (e.hom x)ᴴ = q x := by
  rw [Matrix.conjTranspose_conjTranspose]
  exact e.mul_conjTranspose x

/-! ### The total spaces correspond -/

theorem mulVec_mem_totalSet (e : BundleIso p q) {v : X × (ι → ℂ)} (_hv : v ∈ totalSet p) :
    ((v.1, e.hom v.1 *ᵥ v.2) : X × (κ → ℂ)) ∈ totalSet q := by
  show q v.1 *ᵥ (e.hom v.1 *ᵥ v.2) = e.hom v.1 *ᵥ v.2
  rw [Matrix.mulVec_mulVec, e.hom_mul_left]

theorem conjTranspose_mulVec_mem_totalSet (e : BundleIso p q) {w : X × (κ → ℂ)}
    (_hw : w ∈ totalSet q) : ((w.1, (e.hom w.1)ᴴ *ᵥ w.2) : X × (ι → ℂ)) ∈ totalSet p := by
  show p w.1 *ᵥ ((e.hom w.1)ᴴ *ᵥ w.2) = (e.hom w.1)ᴴ *ᵥ w.2
  have habs : p w.1 * (e.hom w.1)ᴴ = (e.hom w.1)ᴴ := by
    have h : (e.hom w.1 * p w.1)ᴴ = (e.hom w.1)ᴴ :=
      congrArg Matrix.conjTranspose (e.hom_mul_right w.1)
    rwa [Matrix.conjTranspose_mul, p.conjTranspose_eq] at h
  rw [Matrix.mulVec_mulVec, habs]

/-- **Isomorphic bundles have homeomorphic total spaces, over the base.** -/
def totalHomeo (e : BundleIso p q) : Total p ≃ₜ Total q where
  toFun v := ⟨((v : X × (ι → ℂ)).1, e.hom (v : X × (ι → ℂ)).1 *ᵥ (v : X × (ι → ℂ)).2),
    e.mulVec_mem_totalSet v.2⟩
  invFun w := ⟨((w : X × (κ → ℂ)).1, (e.hom (w : X × (κ → ℂ)).1)ᴴ *ᵥ (w : X × (κ → ℂ)).2),
    e.conjTranspose_mulVec_mem_totalSet w.2⟩
  left_inv v := by
    apply Subtype.ext
    refine Prod.ext rfl ?_
    show (e.hom (v : X × (ι → ℂ)).1)ᴴ *ᵥ (e.hom (v : X × (ι → ℂ)).1 *ᵥ (v : X × (ι → ℂ)).2)
      = (v : X × (ι → ℂ)).2
    rw [Matrix.mulVec_mulVec, e.conjTranspose_mul, mem_totalSet_iff.mp v.2]
  right_inv w := by
    apply Subtype.ext
    refine Prod.ext rfl ?_
    show e.hom (w : X × (κ → ℂ)).1 *ᵥ ((e.hom (w : X × (κ → ℂ)).1)ᴴ *ᵥ (w : X × (κ → ℂ)).2)
      = (w : X × (κ → ℂ)).2
    rw [Matrix.mulVec_mulVec, e.mul_conjTranspose, mem_totalSet_iff.mp w.2]
  continuous_toFun :=
    ((continuous_fst.comp continuous_subtype_val).prodMk
      ((e.continuous_hom.comp (continuous_fst.comp continuous_subtype_val)).matrix_mulVec
        (continuous_snd.comp continuous_subtype_val))).subtype_mk _
  continuous_invFun :=
    ((continuous_fst.comp continuous_subtype_val).prodMk
      (((e.continuous_hom.comp (continuous_fst.comp continuous_subtype_val)).matrix_conjTranspose
        ).matrix_mulVec (continuous_snd.comp continuous_subtype_val))).subtype_mk _

theorem totalHomeo_over_base (e : BundleIso p q) (v : Total p) :
    totalPi q (e.totalHomeo v) = totalPi p v := rfl

/-! ### The projective bundles correspond -/

theorem conj_mem_projSet_hom (e : BundleIso p q) {z : X × Matrix ι ι ℂ} (hz : z ∈ projSet p) :
    ((z.1, e.hom z.1 * z.2 * (e.hom z.1)ᴴ) : X × Matrix κ κ ℂ) ∈ projSet q :=
  conj_mem_projSet (e.conjTranspose_mul z.1) (e.hom_mul_left z.1) hz

theorem conj_mem_projSet_conjTranspose (e : BundleIso p q) {z : X × Matrix κ κ ℂ}
    (hz : z ∈ projSet q) :
    ((z.1, (e.hom z.1)ᴴ * z.2 * ((e.hom z.1)ᴴ)ᴴ) : X × Matrix ι ι ℂ) ∈ projSet p :=
  conj_mem_projSet (e.conjTranspose_mul_conjTranspose z.1) (e.conjTranspose_absorb_left z.1) hz

/-- **Isomorphic bundles have homeomorphic projective bundles, over the base.** -/
def projHomeo (e : BundleIso p q) : Proj p ≃ₜ Proj q where
  toFun z := ⟨((z : X × Matrix ι ι ℂ).1,
      e.hom (z : X × Matrix ι ι ℂ).1 * (z : X × Matrix ι ι ℂ).2
        * (e.hom (z : X × Matrix ι ι ℂ).1)ᴴ), e.conj_mem_projSet_hom z.2⟩
  invFun z := ⟨((z : X × Matrix κ κ ℂ).1,
      (e.hom (z : X × Matrix κ κ ℂ).1)ᴴ * (z : X × Matrix κ κ ℂ).2
        * ((e.hom (z : X × Matrix κ κ ℂ).1)ᴴ)ᴴ), e.conj_mem_projSet_conjTranspose z.2⟩
  left_inv z := by
    apply Subtype.ext
    refine Prod.ext rfl ?_
    exact conj_conj (e.conjTranspose_mul (z : X × Matrix ι ι ℂ).1) z.2
  right_inv z := by
    apply Subtype.ext
    refine Prod.ext rfl ?_
    have h := conj_conj (p := q) (a := (e.hom (z : X × Matrix κ κ ℂ).1)ᴴ)
      (e.conjTranspose_mul_conjTranspose (z : X × Matrix κ κ ℂ).1) z.2
    rw [Matrix.conjTranspose_conjTranspose] at h
    exact h
  continuous_toFun :=
    ((continuous_fst.comp continuous_subtype_val).prodMk
      (((e.continuous_hom.comp (continuous_fst.comp continuous_subtype_val)).matrix_mul
        (continuous_snd.comp continuous_subtype_val)).matrix_mul
        ((e.continuous_hom.comp
          (continuous_fst.comp continuous_subtype_val)).matrix_conjTranspose))).subtype_mk _
  continuous_invFun :=
    ((continuous_fst.comp continuous_subtype_val).prodMk
      ((((e.continuous_hom.comp
          (continuous_fst.comp continuous_subtype_val)).matrix_conjTranspose).matrix_mul
        (continuous_snd.comp continuous_subtype_val)).matrix_mul
        (((e.continuous_hom.comp
          (continuous_fst.comp continuous_subtype_val)).matrix_conjTranspose
            ).matrix_conjTranspose))).subtype_mk _

theorem projHomeo_over_base (e : BundleIso p q) (z : Proj p) :
    projPi q (e.projHomeo z) = projPi p z := rfl

/-- **The tautological lines correspond.**  The implementer is `a x · r`, with no
normalization: `(a r)ᴴ (a r) = r p r = r` and `(a r)(a r)ᴴ = a r aᴴ`. -/
def tautIso (e : BundleIso p q) :
    BundleIso (tautLine p) (comap (e.projHomeo).toContinuousMap (tautLine q)) where
  hom z := e.hom (z : X × Matrix ι ι ℂ).1 * (z : X × Matrix ι ι ℂ).2
  continuous_hom :=
    (e.continuous_hom.comp (continuous_fst.comp continuous_subtype_val)).matrix_mul
      (continuous_snd.comp continuous_subtype_val)
  conjTranspose_mul z := by
    have hrH : ((z : X × Matrix ι ι ℂ).2)ᴴ = (z : X × Matrix ι ι ℂ).2 := z.2.1
    have hpr : p (z : X × Matrix ι ι ℂ).1 * (z : X × Matrix ι ι ℂ).2
        = (z : X × Matrix ι ι ℂ).2 := z.2.2.2.2
    have hrp : (z : X × Matrix ι ι ℂ).2 * p (z : X × Matrix ι ι ℂ).1
        = (z : X × Matrix ι ι ℂ).2 := absorb_right_of_mem_projSet z.2
    rw [Matrix.conjTranspose_mul, hrH]
    calc (z : X × Matrix ι ι ℂ).2 * (e.hom (z : X × Matrix ι ι ℂ).1)ᴴ
            * (e.hom (z : X × Matrix ι ι ℂ).1 * (z : X × Matrix ι ι ℂ).2)
        = (z : X × Matrix ι ι ℂ).2 * (((e.hom (z : X × Matrix ι ι ℂ).1)ᴴ
            * e.hom (z : X × Matrix ι ι ℂ).1) * (z : X × Matrix ι ι ℂ).2) := by
          simp only [Matrix.mul_assoc]
      _ = (z : X × Matrix ι ι ℂ).2 * (p (z : X × Matrix ι ι ℂ).1
            * (z : X × Matrix ι ι ℂ).2) := by rw [e.conjTranspose_mul]
      _ = (z : X × Matrix ι ι ℂ).2 * (z : X × Matrix ι ι ℂ).2 := by rw [hpr]
      _ = (z : X × Matrix ι ι ℂ).2 := z.2.2.1
  mul_conjTranspose z := by
    have hrH : ((z : X × Matrix ι ι ℂ).2)ᴴ = (z : X × Matrix ι ι ℂ).2 := z.2.1
    rw [Matrix.conjTranspose_mul, hrH]
    show e.hom (z : X × Matrix ι ι ℂ).1 * (z : X × Matrix ι ι ℂ).2
        * ((z : X × Matrix ι ι ℂ).2 * (e.hom (z : X × Matrix ι ι ℂ).1)ᴴ)
      = e.hom (z : X × Matrix ι ι ℂ).1 * (z : X × Matrix ι ι ℂ).2
        * (e.hom (z : X × Matrix ι ι ℂ).1)ᴴ
    calc e.hom (z : X × Matrix ι ι ℂ).1 * (z : X × Matrix ι ι ℂ).2
            * ((z : X × Matrix ι ι ℂ).2 * (e.hom (z : X × Matrix ι ι ℂ).1)ᴴ)
        = e.hom (z : X × Matrix ι ι ℂ).1 * (((z : X × Matrix ι ι ℂ).2
            * (z : X × Matrix ι ι ℂ).2) * (e.hom (z : X × Matrix ι ι ℂ).1)ᴴ) := by
          simp only [Matrix.mul_assoc]
      _ = e.hom (z : X × Matrix ι ι ℂ).1 * ((z : X × Matrix ι ι ℂ).2
            * (e.hom (z : X × Matrix ι ι ℂ).1)ᴴ) := by rw [z.2.2.1]
      _ = e.hom (z : X × Matrix ι ι ℂ).1 * (z : X × Matrix ι ι ℂ).2
            * (e.hom (z : X × Matrix ι ι ℂ).1)ᴴ := by simp only [Matrix.mul_assoc]

end BundleIso

end Invariance

end Bundle

end CharClass
end GroupApproximation
