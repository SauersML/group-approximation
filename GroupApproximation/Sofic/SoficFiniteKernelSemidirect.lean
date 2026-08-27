import GroupApproximation.Sofic.Sofic
import Mathlib.GroupTheory.SemidirectProduct

/-!
# Soficity of split extensions with finite kernel

If a sofic group `G` acts on a finite group `N`, then `N ⋊ G` is sofic.  The
proof is direct.  A local permutation model `σ` for `G` acts on `N × Y` by

`(n,g) · (a,y) = (n * g(a), σ(g)y)`.

The first coordinate is exactly multiplicative; every defect is confined to
the second coordinate.  This is the finite-stage permanence theorem required
by the Clifford coset tower.
-/

namespace GroupApproximation

variable {N : Type} {G : Type*} [Group N] [Group G]

/-- The elementary permutation model for a semidirect product with finite
normal factor. -/
def finiteKernelPerm (Y : Type*) (φ : G →* MulAut N)
    (σ : G → Equiv.Perm Y) (g : N ⋊[φ] G) : Equiv.Perm (N × Y) where
  toFun p := (g.left * φ g.right p.1, σ g.right p.2)
  invFun p := ((φ g.right).symm (g.left⁻¹ * p.1), (σ g.right)⁻¹ p.2)
  left_inv p := by
    apply Prod.ext <;> simp
  right_inv p := by
    apply Prod.ext <;> simp

@[simp] theorem finiteKernelPerm_apply (Y : Type*) (φ : G →* MulAut N)
    (σ : G → Equiv.Perm Y) (g : N ⋊[φ] G) (p : N × Y) :
    finiteKernelPerm Y φ σ g p =
      (g.left * φ g.right p.1, σ g.right p.2) := rfl

/-- The induced finite carrier. -/
abbrev finiteKernelModel (N : Type) [Fintype N] [DecidableEq N]
    (Y : FiniteModel) : FiniteModel :=
  ⟨N × Y, inferInstance, inferInstance⟩

/-- Multiplication defects in the induced model are exactly the defects of
the quotient model. -/
theorem hammingDistance_finiteKernelPerm_mul
    [Fintype N] [DecidableEq N] (Y : FiniteModel)
    (φ : G →* MulAut N) (σ : G → Equiv.Perm Y) (g h : N ⋊[φ] G)
    (hN : 0 < Fintype.card N) (hY : 0 < Fintype.card Y) :
    hammingDistance (finiteKernelModel N Y)
        (finiteKernelPerm Y φ σ (g * h))
        (finiteKernelPerm Y φ σ g * finiteKernelPerm Y φ σ h) =
      hammingDistance Y (σ (g.right * h.right))
        (σ g.right * σ h.right) := by
  classical
  have hdis : hammingDisagreement
      (finiteKernelPerm Y φ σ (g * h))
      (finiteKernelPerm Y φ σ g * finiteKernelPerm Y φ σ h) =
        (Finset.univ : Finset N).product
          (hammingDisagreement (σ (g.right * h.right))
            (σ g.right * σ h.right)) := by
    ext p
    rw [Finset.product_eq_sprod, Finset.mem_product]
    simp only [Finset.mem_univ, true_and, mem_hammingDisagreement,
      finiteKernelPerm_apply,
      Equiv.Perm.mul_apply, SemidirectProduct.mul_left,
      SemidirectProduct.mul_right, map_mul]
    constructor
    · intro hp hsecond
      apply hp
      apply Prod.ext
      · simp [mul_assoc]
      · exact hsecond
    · intro hp heq
      exact hp (congrArg Prod.snd heq)
  rw [hammingDistance, hammingDistance, hdis, Finset.product_eq_sprod,
    Finset.card_product, Finset.card_univ, Fintype.card_prod]
  push_cast
  have hNR : (Fintype.card N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hYR : (Fintype.card Y : ℝ) ≠ 0 := by exact_mod_cast hY.ne'
  field_simp [hNR, hYR]

/-- Distinct normal coordinates are separated perfectly when the quotient
coordinates agree. -/
theorem hammingDistance_finiteKernelPerm_of_right_eq
    [Fintype N] [DecidableEq N] (Y : FiniteModel)
    (φ : G →* MulAut N) (σ : G → Equiv.Perm Y)
    {g h : N ⋊[φ] G} (hright : g.right = h.right)
    (hleft : g.left ≠ h.left) (hY : 0 < Fintype.card Y) :
    hammingDistance (finiteKernelModel N Y)
      (finiteKernelPerm Y φ σ g) (finiteKernelPerm Y φ σ h) = 1 := by
  classical
  have hdis : hammingDisagreement
      (finiteKernelPerm Y φ σ g) (finiteKernelPerm Y φ σ h) =
      Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro p
    rw [mem_hammingDisagreement]
    intro heq
    apply hleft
    have hfirst : g.left * φ g.right p.1 = h.left * φ h.right p.1 := by
      simpa [finiteKernelPerm_apply] using congrArg Prod.fst heq
    rw [hright] at hfirst
    exact mul_right_cancel hfirst
  rw [hammingDistance, hdis, Finset.card_univ]
  exact div_self (by
    rw [Fintype.card_prod]
    exact_mod_cast (Nat.mul_pos (Fintype.card_pos_iff.mpr ⟨1⟩) hY).ne')

/-- Separation in the quotient model is inherited by the finite-kernel
model. -/
theorem hammingDistance_finiteKernelPerm_right_le
    [Fintype N] [DecidableEq N] (Y : FiniteModel)
    (φ : G →* MulAut N) (σ : G → Equiv.Perm Y) (g h : N ⋊[φ] G)
    (hN : 0 < Fintype.card N) (hY : 0 < Fintype.card Y) :
    hammingDistance Y (σ g.right) (σ h.right) ≤
      hammingDistance (finiteKernelModel N Y)
        (finiteKernelPerm Y φ σ g) (finiteKernelPerm Y φ σ h) := by
  classical
  let D := hammingDisagreement (σ g.right) (σ h.right)
  let E := hammingDisagreement
    (finiteKernelPerm Y φ σ g) (finiteKernelPerm Y φ σ h)
  have hsub : (Finset.univ : Finset N).product D ⊆ E := by
    intro p hp
    rw [Finset.product_eq_sprod, Finset.mem_product] at hp
    rw [mem_hammingDisagreement]
    intro heq
    have hp2 : p.2 ∈ hammingDisagreement (σ g.right) (σ h.right) := by
      simpa [D] using hp.2
    rw [mem_hammingDisagreement] at hp2
    exact hp2 (congrArg Prod.snd heq)
  have hcard := Finset.card_le_card hsub
  rw [hammingDistance, hammingDistance]
  change (D.card : ℝ) / Fintype.card Y ≤
    (E.card : ℝ) / Fintype.card (N × Y)
  rw [Fintype.card_prod]
  push_cast
  have hNreal : (0 : ℝ) < Fintype.card N := by exact_mod_cast hN
  have hYreal : (0 : ℝ) < Fintype.card Y := by exact_mod_cast hY
  rw [div_le_div_iff₀ hYreal (mul_pos hNreal hYreal)]
  have hcard' : (Fintype.card N : ℝ) * D.card ≤ E.card := by
    exact_mod_cast (by simpa using hcard)
  nlinarith

/-- **Split finite-kernel permanence for soficity.** -/
theorem isSofic_finiteKernel_semidirectProduct
    (φ : G →* MulAut N) [Finite N] (hG : IsSofic G) :
    IsSofic (N ⋊[φ] G) := by
  classical
  letI : Fintype N := Fintype.ofFinite N
  intro F ε hε
  let T : Finset G := F.image SemidirectProduct.right
  obtain ⟨M⟩ := hG T ε hε
  refine ⟨{
    carrier := finiteKernelModel N M.carrier
    nonempty := by
      rw [Fintype.card_prod]
      exact Nat.mul_pos (Fintype.card_pos_iff.mpr ⟨1⟩) M.nonempty
    map := finiteKernelPerm M.carrier φ M.map
    multiplicative := ?_
    separated := ?_ }⟩
  · intro g hg h hh
    rw [hammingDistance_finiteKernelPerm_mul
      M.carrier φ M.map g h (Fintype.card_pos_iff.mpr ⟨1⟩) M.nonempty]
    exact M.multiplicative _ (Finset.mem_image_of_mem _ hg)
      _ (Finset.mem_image_of_mem _ hh)
  · intro g hg h hh hne
    by_cases hright : g.right = h.right
    · rw [hammingDistance_finiteKernelPerm_of_right_eq M.carrier φ M.map
          hright (fun hleft ↦ hne (SemidirectProduct.ext hleft hright))
          M.nonempty]
      linarith
    · exact le_trans
        (M.separated _ (Finset.mem_image_of_mem _ hg)
          _ (Finset.mem_image_of_mem _ hh) hright)
        (hammingDistance_finiteKernelPerm_right_le M.carrier φ M.map g h
          (Fintype.card_pos_iff.mpr ⟨1⟩) M.nonempty)

end GroupApproximation
