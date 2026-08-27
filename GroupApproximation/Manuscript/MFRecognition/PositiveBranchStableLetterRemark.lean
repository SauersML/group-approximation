import GroupApproximation.Manuscript.MFRecognition.PositiveBranchFiniteQuotients

/-!
# The remark after `lem:positive-branch`: the second coordinate is needed

> *"The second coordinate of `G_n` is needed: with `λ_n(v) = 1` the two copies
> of `F` in `S_e` would have the same image, and the kernel condition would
> fail on `i(f) v i(f)⁻¹ v⁻¹` for `f ∉ N₊`."*

`PositiveBranchFiniteQuotients.ropeLambda` sends the stable letter `v` to the
swap `σ` of `G_n = (C_n × C_n) ⋊ C₂`.  Here the alternative with `λ_n(v) = 1`
is written down (`flatLambda`), and the printed failure is proved: the
commutator `i(f) v i(f)⁻¹ v⁻¹` lies in `S_e`, is killed by `flatLambda`, and
is sent by `α_e` to `q_e(f)`, so whenever `β_n(q_e(f)) ≠ 1` — which is the
case for `f ∉ N₊` and `n` large — it lies in `ker(λ_n|_{S_e})` but not in
`ker(β_n ∘ α_e)`.
-/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace Recognition

noncomputable section

variable {K0 F P C : Type} [Group K0] [Group F] [Group P] [Group C]

/-- The would-be `λ_n` with `λ_n(v) = 1`: the base map alone, with the stable
letter sent to the identity.  It is a homomorphism because the base map is
constant on `L_e`-conjugation, trivially. -/
def flatLambda (L0 : Subgroup K0) (psi : F →* P) (r : P →* C) :
    CentralRope L0 psi →* C × C :=
  HNNExtension.lift (baseHom psi r) 1 (fun a => by simp)

theorem flatLambda_of (L0 : Subgroup K0) (psi : F →* P) (r : P →* C)
    (x : RopeBase K0 F P) :
    flatLambda L0 psi r (HNNExtension.of x) = baseHom psi r x :=
  HNNExtension.lift_of _ _ _ _

theorem flatLambda_stable (L0 : Subgroup K0) (psi : F →* P) (r : P →* C) :
    flatLambda L0 psi r (ropeStable L0 psi) = 1 := by
  unfold ropeStable
  rw [map_inv, flatLambda, HNNExtension.lift_t, inv_one]

/-- The printed commutator `i(f) v i(f)⁻¹ v⁻¹ = i(f) · (v i(f) v⁻¹)⁻¹`, read
in `S_e`. -/
def stableCommutatorS (L0 : Subgroup K0) (psi : F →* P) (i0 : F →* K0) (f : F) :
    ↥(ropeSubgroup L0 psi i0) :=
  ropeGenS L0 psi i0 f * (ropeGenConjS L0 psi i0 f)⁻¹

/-- With `λ_n(v) = 1` the two copies of `F` have the same image, so the
commutator is killed. -/
theorem flatLambda_stableCommutator (L0 : Subgroup K0) (psi : F →* P)
    (r : P →* C) (i0 : F →* K0) (f : F) :
    flatLambda L0 psi r (stableCommutatorS L0 psi i0 f : CentralRope L0 psi) = 1 := by
  simp only [stableCommutatorS, Subgroup.coe_mul, Subgroup.coe_inv, coe_ropeGenS,
    coe_ropeGenConjS, ropeGenConj_apply, map_mul, map_inv, flatLambda_stable,
    inv_one, one_mul, mul_one, mul_inv_cancel]

/-- `α_e` sends the commutator to `q_e(f)`: `α_e(i(f)) = q_e(f)` and
`α_e(v i(f) v⁻¹) = 1`. -/
theorem alpha_stableCommutator (L0 : Subgroup K0) (psi : F →* P) (i0 : F →* K0)
    {Q : Type} [Group Q] (alpha : ↥(ropeSubgroup L0 psi i0) →* Q) (q : F →* Q)
    (hgen : ∀ f, alpha (ropeGenS L0 psi i0 f) = q f)
    (hconj : ∀ f, alpha (ropeGenConjS L0 psi i0 f) = 1) (f : F) :
    alpha (stableCommutatorS L0 psi i0 f) = q f := by
  rw [stableCommutatorS, map_mul, map_inv, hgen, hconj, inv_one, mul_one]

/-- **The printed remark.**  With `λ_n(v) = 1`, the commutator
`i(f) v i(f)⁻¹ v⁻¹` lies in `ker(λ_n|_{S_e})` but, as soon as
`β_n(q_e(f)) ≠ 1`, not in `ker(β_n ∘ α_e)`: the kernel condition of
`lem:tensor-sync` fails. -/
theorem flatLambda_kernel_condition_fails (L0 : Subgroup K0) (psi : F →* P)
    (r : P →* C) (i0 : F →* K0)
    {Q B : Type} [Group Q] [Group B] (alpha : ↥(ropeSubgroup L0 psi i0) →* Q)
    (q : F →* Q)
    (hgen : ∀ f, alpha (ropeGenS L0 psi i0 f) = q f)
    (hconj : ∀ f, alpha (ropeGenConjS L0 psi i0 f) = 1)
    (beta : Q →* B) (f : F) (hf : beta (q f) ≠ 1) :
    stableCommutatorS L0 psi i0 f ∈
        ((flatLambda L0 psi r).comp (ropeSubgroup L0 psi i0).subtype).ker ∧
      stableCommutatorS L0 psi i0 f ∉ (beta.comp alpha).ker := by
  refine ⟨?_, ?_⟩
  · rw [MonoidHom.mem_ker]
    show flatLambda L0 psi r (stableCommutatorS L0 psi i0 f : CentralRope L0 psi) = 1
    exact flatLambda_stableCommutator L0 psi r i0 f
  · rw [MonoidHom.mem_ker, MonoidHom.comp_apply,
      alpha_stableCommutator L0 psi i0 alpha q hgen hconj]
    exact hf

end

end Recognition
end MFRecognition
end Manuscript
end GroupApproximation
