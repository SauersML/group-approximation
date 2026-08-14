import GroupApproximation.Sofic.SoficDirectedUnion
import GroupApproximation.Sofic.SoficFiniteKernelSemidirect
import GroupApproximation.Sofic.SoficTransfer

/-!
# Semidirect products with a locally finite invariant kernel

`isSofic_finiteKernel_semidirectProduct` needs the whole normal factor to be
finite.  The lamp layer of the witness tower is only *locally* finite: a
finite window of lamps sits in a finite lamp subgroup, and that subgroup is
invariant under a suitable subgroup of the acting group -- for the witness,
under one level of the telescope, because the levels are commensurable and
therefore have finite orbits on the coset space of sites.

This file packages that pattern.  If every finite window of `N ⋊ G` can be
enclosed in a finite `G`-invariant subgroup of `N` together with a sofic
subgroup of `G` acting on it, then `N ⋊ G` is sofic: the enclosing pair spans
a subgroup isomorphic to an honest finite-kernel semidirect product, and
soficity is local over subgroups.
-/

namespace GroupApproximation

variable {N : Type} {G : Type*} [Group N] [Group G]

/-- The action of an invariant subgroup pair, restricted to the kernel. -/
def restrictAut (φ : G →* MulAut N) (K : Subgroup N) (H : Subgroup G)
    (hinv : ∀ h ∈ H, ∀ n ∈ K, φ h n ∈ K) : H →* MulAut K where
  toFun h :=
    { toFun := fun k ↦ ⟨φ h k, hinv h h.2 k k.2⟩
      invFun := fun k ↦ ⟨φ h⁻¹ k, hinv (h : G)⁻¹ (H.inv_mem h.2) k k.2⟩
      left_inv := by
        intro k
        apply Subtype.ext
        show φ (h : G)⁻¹ (φ (h : G) (k : N)) = (k : N)
        rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one]
        rfl
      right_inv := by
        intro k
        apply Subtype.ext
        show φ (h : G) (φ (h : G)⁻¹ (k : N)) = (k : N)
        rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one]
        rfl
      map_mul' := by
        intro a b
        apply Subtype.ext
        show φ (h : G) ((a : N) * b) = φ (h : G) a * φ (h : G) b
        exact map_mul _ _ _ }
  map_one' := by
    apply MulEquiv.ext
    intro k
    apply Subtype.ext
    show φ ((1 : H) : G) (k : N) = (k : N)
    rw [Subgroup.coe_one, map_one]
    rfl
  map_mul' a b := by
    apply MulEquiv.ext
    intro k
    apply Subtype.ext
    show φ ((a * b : H) : G) (k : N) = φ (a : G) (φ (b : G) (k : N))
    rw [Subgroup.coe_mul, map_mul]
    rfl

/-- The enclosing subgroup pair spans a copy of the finite-kernel semidirect
product inside `N ⋊ G`. -/
def inclSemidirect (φ : G →* MulAut N) (K : Subgroup N) (H : Subgroup G)
    (hinv : ∀ h ∈ H, ∀ n ∈ K, φ h n ∈ K) :
    K ⋊[restrictAut φ K H hinv] H →* N ⋊[φ] G :=
  SemidirectProduct.lift
    ((SemidirectProduct.inl : N →* N ⋊[φ] G).comp K.subtype)
    ((SemidirectProduct.inr : G →* N ⋊[φ] G).comp H.subtype)
    (by
      intro h
      apply MonoidHom.ext
      intro k
      show (SemidirectProduct.inl (((restrictAut φ K H hinv) h k : K) : N) :
          N ⋊[φ] G) =
        SemidirectProduct.inr (h : G) * SemidirectProduct.inl (k : N) *
          (SemidirectProduct.inr (h : G))⁻¹
      rw [← map_inv, ← SemidirectProduct.inl_aut]
      rfl)

@[simp] theorem inclSemidirect_apply (φ : G →* MulAut N) (K : Subgroup N)
    (H : Subgroup G) (hinv : ∀ h ∈ H, ∀ n ∈ K, φ h n ∈ K)
    (g : K ⋊[restrictAut φ K H hinv] H) :
    inclSemidirect φ K H hinv g =
      ⟨(g.left : N), (g.right : G)⟩ := by
  show SemidirectProduct.inl ((g.left : K) : N) *
      SemidirectProduct.inr ((g.right : H) : G) = _
  apply SemidirectProduct.ext <;> simp

theorem inclSemidirect_injective (φ : G →* MulAut N) (K : Subgroup N)
    (H : Subgroup G) (hinv : ∀ h ∈ H, ∀ n ∈ K, φ h n ∈ K) :
    Function.Injective (inclSemidirect φ K H hinv) := by
  intro a b hab
  rw [inclSemidirect_apply, inclSemidirect_apply] at hab
  have hleft : (a.left : N) = (b.left : N) := congrArg SemidirectProduct.left hab
  have hright : (a.right : G) = (b.right : G) :=
    congrArg SemidirectProduct.right hab
  exact SemidirectProduct.ext (Subtype.ext hleft) (Subtype.ext hright)

/-- **Soficity for a locally finite invariant kernel.** -/
theorem isSofic_semidirectProduct_of_invariant_finite
    (φ : G →* MulAut N)
    (hlocal : ∀ F : Finset (N ⋊[φ] G), ∃ (K : Subgroup N) (H : Subgroup G),
      Finite K ∧ IsSofic H ∧ (∀ h ∈ H, ∀ n ∈ K, φ h n ∈ K) ∧
        (∀ g ∈ F, g.left ∈ K ∧ g.right ∈ H)) :
    IsSofic (N ⋊[φ] G) := by
  classical
  apply isSofic_of_every_finset_mem_sofic_subgroup
  intro F
  obtain ⟨K, H, hKfin, hHsofic, hinv, hmem⟩ := hlocal F
  haveI : Finite K := hKfin
  refine ⟨(inclSemidirect φ K H hinv).range, ?_, ?_⟩
  · have hmodel : IsSofic (K ⋊[restrictAut φ K H hinv] H) :=
      isSofic_finiteKernel_semidirectProduct _ hHsofic
    have hequiv : (K ⋊[restrictAut φ K H hinv] H) ≃*
        (inclSemidirect φ K H hinv).range :=
      MonoidHom.ofInjective (inclSemidirect_injective φ K H hinv)
    exact isSofic_of_injective hequiv.symm.toMonoidHom hequiv.symm.injective
      hmodel
  · intro g hg
    obtain ⟨hleft, hright⟩ := hmem g hg
    refine ⟨⟨⟨g.left, hleft⟩, ⟨g.right, hright⟩⟩, ?_⟩
    rw [inclSemidirect_apply]

end GroupApproximation
