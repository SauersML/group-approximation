import GroupApproximation.BooneHigman.Metabelian.VdKOmegaFreeDecomp
import Mathlib.GroupTheory.Coset.Defs
import Mathlib.Algebra.Group.Commutator
import GroupApproximation.Meta.AxiomGuard

/-!
# `vdkOmegaFree`, part 2: orbit spaces of an injective hom, and the glued bijection

Lane `bh-met-93j`.  Generic group theory, unconditional.

* `vdkOmegaFree_Inter E f γ`: the permutation `f` of `Ω` is carried by `E : Ω → Γ` to left
  multiplication by `γ`.  Products, inverses and hence commutators are carried along
  (`vdkOmegaFree_commutator_eq`): this turns one identity in `Γ` into one identity of
  permutations.
* `vdkOmegaFree_Orb π`: for `π : P →* Γ`, the orbit space `π(P) \ Γ` of left
  multiplication.  `vdkOmegaFree_E π : P × Orb π → Γ`, `(p, x) ↦ π p · out x`, is onto,
  and injective when `π` is (`vdkOmegaFree_Eequiv`).  It carries left multiplication by
  `p` to that by `π p`.
* `vdkOmegaFree_Psi π π'`: for two injective homs out of `N ⋊[φ] G` and `N' ⋊[φ'] G` that
  agree on `G`, the composite `E'⁻¹ ∘ E` is `G`-equivariant
  (`vdkOmegaFree_Psi_equivariant`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open scoped commutatorElement

section Inter

variable {Ω Γ : Type*} [Group Γ]

/-- `E (f ω) = γ * E ω` for every `ω`. -/
def vdkOmegaFree_Inter (E : Ω → Γ) (f : Equiv.Perm Ω) (γ : Γ) : Prop :=
  ∀ ω, E (f ω) = γ * E ω

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaFree_Inter

variable {E : Ω → Γ}

theorem vdkOmegaFree_inter_mul {f g : Equiv.Perm Ω} {γ δ : Γ} (hf : vdkOmegaFree_Inter E f γ)
    (hg : vdkOmegaFree_Inter E g δ) : vdkOmegaFree_Inter E (f * g) (γ * δ) := by
  intro ω
  rw [Equiv.Perm.mul_apply, hf (g ω), hg ω, mul_assoc]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaFree_inter_mul

theorem vdkOmegaFree_inter_inv {f : Equiv.Perm Ω} {γ : Γ} (hf : vdkOmegaFree_Inter E f γ) :
    vdkOmegaFree_Inter E f⁻¹ γ⁻¹ := by
  intro ω
  have h : f (f⁻¹ ω) = ω := f.apply_symm_apply ω
  have e := hf (f⁻¹ ω)
  rw [h] at e
  exact eq_inv_mul_of_mul_eq e.symm

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaFree_inter_inv

/-- **Commutators are carried along.**  If `E` is injective and carries `a`, `b`, `c` to left
multiplication by `γa`, `γb`, `γc`, then `⁅γa, γb⁆ = γc` gives `⁅a, b⁆ = c`. -/
theorem vdkOmegaFree_commutator_eq (hE : Function.Injective E) {a b c : Equiv.Perm Ω}
    {γa γb γc : Γ} (ha : vdkOmegaFree_Inter E a γa) (hb : vdkOmegaFree_Inter E b γb)
    (hc : vdkOmegaFree_Inter E c γc) (hγ : ⁅γa, γb⁆ = γc) : ⁅a, b⁆ = c := by
  have h := vdkOmegaFree_inter_mul (vdkOmegaFree_inter_mul (vdkOmegaFree_inter_mul ha hb)
    (vdkOmegaFree_inter_inv ha)) (vdkOmegaFree_inter_inv hb)
  refine Equiv.ext fun ω ↦ hE ?_
  rw [commutatorElement_def, h ω, hc ω, ← hγ, commutatorElement_def]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaFree_commutator_eq

end Inter

section Orb

variable {P Γ : Type*} [Group P] [Group Γ] (π : P →* Γ)

/-- The orbit space `π(P) \ Γ` of left multiplication by `π(P)` on `Γ`. -/
abbrev vdkOmegaFree_Orb : Type _ := Quotient (QuotientGroup.rightRel π.range)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaFree_Orb

/-- `(p, x) ↦ π p · out x`. -/
noncomputable def vdkOmegaFree_E (c : P × vdkOmegaFree_Orb π) : Γ :=
  π c.1 * Quotient.out c.2

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaFree_E

theorem vdkOmegaFree_E_mul (p a : P) (x : vdkOmegaFree_Orb π) :
    vdkOmegaFree_E π (p * a, x) = π p * vdkOmegaFree_E π (a, x) := by
  show π (p * a) * Quotient.out x = π p * (π a * Quotient.out x)
  rw [map_mul, mul_assoc]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaFree_E_mul

theorem vdkOmegaFree_E_surjective : Function.Surjective (vdkOmegaFree_E π) := by
  intro γ
  have h := QuotientGroup.rightRel_apply.mp
    (Quotient.mk_out (s := QuotientGroup.rightRel π.range) γ)
  obtain ⟨p, hp⟩ := MonoidHom.mem_range.mp h
  refine ⟨(p, Quotient.mk (QuotientGroup.rightRel π.range) γ), ?_⟩
  show π p * Quotient.out (Quotient.mk (QuotientGroup.rightRel π.range) γ) = γ
  rw [hp, inv_mul_cancel_right]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaFree_E_surjective

theorem vdkOmegaFree_E_injective (hπ : Function.Injective π) :
    Function.Injective (vdkOmegaFree_E π) := by
  rintro ⟨p, x⟩ ⟨p', x'⟩ h
  have h' : π p * Quotient.out x = π p' * Quotient.out x' := h
  have hmem : Quotient.out x' * (Quotient.out x)⁻¹ ∈ π.range := by
    refine MonoidHom.mem_range.mpr ⟨p'⁻¹ * p, ?_⟩
    rw [map_mul, map_inv, inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h', mul_inv_cancel_right]
  have hr : QuotientGroup.rightRel π.range (Quotient.out x) (Quotient.out x') :=
    QuotientGroup.rightRel_apply.mpr hmem
  have hx : x = x' :=
    (Quotient.out_eq x).symm.trans ((Quotient.eq.mpr hr).trans (Quotient.out_eq x'))
  subst hx
  exact Prod.ext (hπ (mul_right_cancel h')) rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaFree_E_injective

/-- For injective `π`, the bijection `P × π(P) \ Γ ≃ Γ`. -/
noncomputable def vdkOmegaFree_Eequiv (hπ : Function.Injective π) :
    P × vdkOmegaFree_Orb π ≃ Γ :=
  Equiv.ofBijective (vdkOmegaFree_E π)
    ⟨vdkOmegaFree_E_injective π hπ, vdkOmegaFree_E_surjective π⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaFree_Eequiv

theorem vdkOmegaFree_Eequiv_apply (hπ : Function.Injective π) (c : P × vdkOmegaFree_Orb π) :
    vdkOmegaFree_Eequiv π hπ c = vdkOmegaFree_E π c :=
  rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaFree_Eequiv_apply

end Orb

section Glue

variable {N G N' Γ : Type*} [Group N] [Group G] [Group N'] [Group Γ]
  {φ : G →* MulAut N} {φ' : G →* MulAut N'}
  (π : N ⋊[φ] G →* Γ) (π' : N' ⋊[φ'] G →* Γ)
  (hπ : Function.Injective π) (hπ' : Function.Injective π')

/-- `Ψ = E'⁻¹ ∘ E`. -/
noncomputable def vdkOmegaFree_Psi :
    (N ⋊[φ] G) × vdkOmegaFree_Orb π ≃ (N' ⋊[φ'] G) × vdkOmegaFree_Orb π' :=
  (vdkOmegaFree_Eequiv π hπ).trans (vdkOmegaFree_Eequiv π' hπ').symm

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaFree_Psi

theorem vdkOmegaFree_E_Psi (ω : (N ⋊[φ] G) × vdkOmegaFree_Orb π) :
    vdkOmegaFree_E π' (vdkOmegaFree_Psi π π' hπ hπ' ω) = vdkOmegaFree_E π ω :=
  (vdkOmegaFree_Eequiv π' hπ').apply_symm_apply (vdkOmegaFree_Eequiv π hπ ω)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaFree_E_Psi

theorem vdkOmegaFree_E_Psi_symm (ω' : (N' ⋊[φ'] G) × vdkOmegaFree_Orb π') :
    vdkOmegaFree_E π ((vdkOmegaFree_Psi π π' hπ hπ').symm ω') = vdkOmegaFree_E π' ω' :=
  (vdkOmegaFree_Eequiv π hπ).apply_symm_apply (vdkOmegaFree_Eequiv π' hπ' ω')

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaFree_E_Psi_symm

/-- **`Ψ` is `G`-equivariant** once `π`, `π'` agree on `G`. -/
theorem vdkOmegaFree_Psi_equivariant
    (hinr : ∀ g : G, π (SemidirectProduct.inr g) = π' (SemidirectProduct.inr g)) :
    vdkOmegaFree_Equivariant (vdkOmegaFree_Psi π π' hπ hπ') := by
  intro g p x
  apply vdkOmegaFree_E_injective π' hπ'
  rw [vdkOmegaFree_E_Psi, vdkOmegaFree_E_mul, vdkOmegaFree_E_mul, hinr]
  exact congrArg (π' (SemidirectProduct.inr g) * ·)
    (vdkOmegaFree_E_Psi π π' hπ hπ' (p, x)).symm

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaFree_Psi_equivariant

/-- Left multiplication by `q` on the `Ψ`-side is carried by `E` to left multiplication by
`π' q`. -/
theorem vdkOmegaFree_E_Psi_symm_mul (q : N' ⋊[φ'] G)
    (ω : (N ⋊[φ] G) × vdkOmegaFree_Orb π) :
    vdkOmegaFree_E π ((vdkOmegaFree_Psi π π' hπ hπ').symm
      (q * (vdkOmegaFree_Psi π π' hπ hπ' ω).1, (vdkOmegaFree_Psi π π' hπ hπ' ω).2)) =
      π' q * vdkOmegaFree_E π ω := by
  rw [vdkOmegaFree_E_Psi_symm, vdkOmegaFree_E_mul]
  exact congrArg (π' q * ·) (vdkOmegaFree_E_Psi π π' hπ hπ' ω)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaFree_E_Psi_symm_mul

end Glue

end GroupApproximation.BooneHigman.Metabelian.ElemFP
