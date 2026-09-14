import GroupApproximation.Kazhdan.KazhdanBimoduleRigidity
import GroupApproximation.Analysis.TracialConjugationExists
import GroupApproximation.Meta.AxiomGuard
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Left and right actions of unitary representations on a tracial standard form

For the Ozawa step of `simple_kazhdan_sofic_group.tex` (origin/main 696c4b602, tex l.544–546), a group of
unitaries of a von Neumann algebra `M` acts on `L²(M)` from the left and from the right.  Here `M` acts on
`H` with a unit cyclic separating tracial vector `Ω` (`IsTracialStandardForm M Ω`), so `H` plays the role of
`L²(M)`, and the modular conjugation `J` (`TracialConjugation`, constructed in `TracialConjugationExists`)
turns left multiplication into right multiplication: `J u J (TΩ) = T u⋆ Ω`.

For `u : Γ →* unitary M`:

* `leftRep u g = u(g)`, as a linear isometry equivalence of `H`;
* `rightRep c u g = J u(g) J`, a homomorphism because `J` is an involution;
* `leftRep_mul_rightRep_comm`: the actions commute, since `J M J ⊆ M′` (`conjOp_mem_commutant`);
* `rightRep_omega`: `J u(g) J Ω = u(g⁻¹) Ω`;
* `ker_leftRep`, `ker_rightRep`: both actions have the kernel of `u`;
* `eq_one_of_leftRep_omega`: `u(g) Ω = Ω` forces `u(g) = 1`, as `Ω` is separating.

These are the hypotheses of `KazhdanBimoduleRigidity.bimodule_rigidity`.
-/

set_option linter.unusedSectionVars false

namespace GroupApproximation
namespace TracialStandardFormBimodule

open TracialStandardForm

universe v w

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} {Ω : H}

/-- The unitaries of `M` as unitaries of `B(H)`. -/
def opUnitary : unitary ↥M.toStarSubalgebra →* unitary (H →L[ℂ] H) where
  toFun w := ⟨((w : ↥M.toStarSubalgebra) : H →L[ℂ] H), by
    rw [Unitary.mem_iff]
    exact ⟨congrArg Subtype.val (Unitary.coe_star_mul_self w),
      congrArg Subtype.val (Unitary.coe_mul_star_self w)⟩⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

variable {Γ : Type w} [Group Γ]

/-- The left action `ξ ↦ u(g) ξ`. -/
noncomputable def leftRep (u : Γ →* unitary ↥M.toStarSubalgebra) : Γ →* (H ≃ₗᵢ[ℂ] H) :=
  Unitary.linearIsometryEquiv.toMonoidHom.comp (opUnitary.comp u)

theorem leftRep_apply (u : Γ →* unitary ↥M.toStarSubalgebra) (g : Γ) (x : H) :
    leftRep u g x = ((u g : ↥M.toStarSubalgebra) : H →L[ℂ] H) x :=
  rfl

section Conj

variable (c : TracialConjugation M Ω)

/-- Conjugation of an isometry by the modular conjugation, `x ↦ J (e (J x))`. -/
noncomputable def conjIsometry (e : H ≃ₗᵢ[ℂ] H) : H ≃ₗᵢ[ℂ] H where
  toFun x := c.J (e (c.J x))
  invFun x := c.J (e.symm (c.J x))
  map_add' x y := by
    show c.J (e (c.J (x + y))) = c.J (e (c.J x)) + c.J (e (c.J y))
    rw [c.map_add, map_add, c.map_add]
  map_smul' z x := by
    show c.J (e (c.J (z • x))) = (RingHom.id ℂ) z • c.J (e (c.J x))
    rw [RingHom.id_apply, c.map_smul, map_smul, c.map_smul, Complex.conj_conj]
  left_inv x := by
    show c.J (e.symm (c.J (c.J (e (c.J x))))) = x
    rw [c.invol, LinearIsometryEquiv.symm_apply_apply, c.invol]
  right_inv x := by
    show c.J (e (c.J (c.J (e.symm (c.J x))))) = x
    rw [c.invol, LinearIsometryEquiv.apply_symm_apply, c.invol]
  norm_map' x := by
    show ‖c.J (e (c.J x))‖ = ‖x‖
    rw [c.norm_map, LinearIsometryEquiv.norm_map, c.norm_map]

/-- Conjugation by `J`, as a group homomorphism of isometries. -/
noncomputable def conjHom : (H ≃ₗᵢ[ℂ] H) →* (H ≃ₗᵢ[ℂ] H) where
  toFun := conjIsometry c
  map_one' := LinearIsometryEquiv.ext fun x ↦ by
    show c.J (c.J x) = x
    exact c.invol x
  map_mul' e₁ e₂ := LinearIsometryEquiv.ext fun x ↦ by
    show c.J (e₁ (e₂ (c.J x))) = c.J (e₁ (c.J (c.J (e₂ (c.J x)))))
    rw [c.invol]

theorem conjHom_eq_one_iff (e : H ≃ₗᵢ[ℂ] H) : conjHom c e = 1 ↔ e = 1 := by
  constructor
  · intro h
    refine LinearIsometryEquiv.ext fun x ↦ ?_
    have hx := congrArg (fun f : H ≃ₗᵢ[ℂ] H ↦ f (c.J x)) h
    change c.J (e (c.J (c.J x))) = c.J x at hx
    rw [c.invol] at hx
    have hx' := congrArg c.J hx
    rw [c.invol, c.invol] at hx'
    exact hx'
  · intro h
    rw [h, map_one]

/-- The right action `J u(g) J`, which is right multiplication by `u(g)⋆` on `L²(M)`. -/
noncomputable def rightRep (u : Γ →* unitary ↥M.toStarSubalgebra) : Γ →* (H ≃ₗᵢ[ℂ] H) :=
  (conjHom c).comp (leftRep u)

theorem rightRep_apply (u : Γ →* unitary ↥M.toStarSubalgebra) (g : Γ) (x : H) :
    rightRep c u g x = c.J (((u g : ↥M.toStarSubalgebra) : H →L[ℂ] H) (c.J x)) :=
  rfl

theorem J_omega : c.J Ω = Ω := by
  have h := c.map_orbit 1 (one_mem M)
  simpa using h

/-- `J u(g) J Ω = u(g⁻¹) Ω`: the right and left actions agree on the trace vector. -/
theorem rightRep_omega (u : Γ →* unitary ↥M.toStarSubalgebra) (g : Γ) :
    rightRep c u g Ω = leftRep u g⁻¹ Ω := by
  have hmem : ((u g : ↥M.toStarSubalgebra) : H →L[ℂ] H) ∈ M := (u g : ↥M.toStarSubalgebra).2
  have hinv : ((u g⁻¹ : unitary ↥M.toStarSubalgebra) : ↥M.toStarSubalgebra) =
      star ((u g : unitary ↥M.toStarSubalgebra) : ↥M.toStarSubalgebra) :=
    (congrArg Subtype.val (map_inv u g)).trans rfl
  rw [rightRep_apply, J_omega c, c.map_orbit _ hmem, leftRep_apply]
  exact (congrArg (fun T : ↥M.toStarSubalgebra ↦ (T : H →L[ℂ] H) Ω) hinv).symm

/-- The left and right actions commute, as `J M J ⊆ M′`. -/
theorem leftRep_mul_rightRep_comm (hsf : IsTracialStandardForm M Ω)
    (u₁ u₂ : Γ →* unitary ↥M.toStarSubalgebra) (g h : Γ) :
    leftRep u₁ g * rightRep c u₂ h = rightRep c u₂ h * leftRep u₁ g := by
  have hcomm := (VonNeumannAlgebra.mem_commutant_iff.mp
    (conjOp_mem_commutant c hsf (u₂ h : ↥M.toStarSubalgebra).2)) _
      (u₁ g : ↥M.toStarSubalgebra).2
  refine LinearIsometryEquiv.ext fun x ↦ ?_
  show ((u₁ g : ↥M.toStarSubalgebra) : H →L[ℂ] H)
      (c.J (((u₂ h : ↥M.toStarSubalgebra) : H →L[ℂ] H) (c.J x))) =
    c.J (((u₂ h : ↥M.toStarSubalgebra) : H →L[ℂ] H)
      (c.J (((u₁ g : ↥M.toStarSubalgebra) : H →L[ℂ] H) x)))
  exact congrArg (fun T : H →L[ℂ] H ↦ T x) hcomm

theorem ker_rightRep (u : Γ →* unitary ↥M.toStarSubalgebra) :
    (rightRep c u).ker = (leftRep u).ker := by
  ext g
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
  exact conjHom_eq_one_iff c _

end Conj

theorem leftRep_eq_one_iff (u : Γ →* unitary ↥M.toStarSubalgebra) (g : Γ) :
    leftRep u g = 1 ↔ u g = 1 := by
  constructor
  · intro h
    apply Subtype.ext
    apply Subtype.ext
    refine ContinuousLinearMap.ext fun x ↦ ?_
    exact congrArg (fun e : H ≃ₗᵢ[ℂ] H ↦ e x) h
  · intro h
    refine LinearIsometryEquiv.ext fun x ↦ ?_
    calc leftRep u g x = ((1 : unitary ↥M.toStarSubalgebra) : ↥M.toStarSubalgebra) x := by
          rw [leftRep_apply, h]
      _ = x := rfl

theorem ker_leftRep (u : Γ →* unitary ↥M.toStarSubalgebra) : (leftRep u).ker = u.ker := by
  ext g
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
  exact leftRep_eq_one_iff u g

/-- `u(g) Ω = Ω` forces `u(g) = 1`, as `Ω` is separating. -/
theorem eq_one_of_leftRep_omega (hsf : IsTracialStandardForm M Ω)
    (u : Γ →* unitary ↥M.toStarSubalgebra) (g : Γ) (h : leftRep u g Ω = Ω) : u g = 1 := by
  have hmem : ((u g : ↥M.toStarSubalgebra) : H →L[ℂ] H) - 1 ∈ M :=
    sub_mem (u g : ↥M.toStarSubalgebra).2 (one_mem M)
  have h0 : ((u g : ↥M.toStarSubalgebra) : H →L[ℂ] H) - 1 = 0 := by
    refine hsf.separating _ hmem ?_
    show ((u g : ↥M.toStarSubalgebra) : H →L[ℂ] H) Ω - Ω = 0
    exact sub_eq_zero.mpr h
  apply Subtype.ext
  apply Subtype.ext
  exact sub_eq_zero.mp h0

#audit_axioms rightRep_omega
#audit_axioms leftRep_mul_rightRep_comm
#audit_axioms ker_rightRep
#audit_axioms eq_one_of_leftRep_omega

end TracialStandardFormBimodule
end GroupApproximation
