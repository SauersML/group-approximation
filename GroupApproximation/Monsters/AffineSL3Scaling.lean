import GroupApproximation.Monsters.AffineSL3Doubling

/-!
# Integral scaling in `ℤ³ ⋊ SL₃(ℤ)`

This file parameterizes the concrete affine calculation used in manuscript
Theorem `thm:family`.  For every natural number `m ≥ 2`, scaling the
translation coordinate by `m` and fixing the linear coordinate is an
injective endomorphism of the actual group `ℤ³ ⋊ SL₃(ℤ)`.  Its image consists
exactly of elements whose translation coordinate is divisible by `m`, and the
first standard translation is not in that image.

No presentation or property-(T) input is used here.
-/

namespace GroupApproximation
namespace AffineSL3Scaling

open AffineSL3Doubling

/-- Multiplication by `m` on the additive lattice. -/
def scaleAdd (m : ℕ) : Lattice →+ Lattice :=
  nsmulAddMonoidHom m

/-- Multiplication by `m` on the multiplicative lattice. -/
def scaleMul (m : ℕ) : Multiplicative Lattice →* Multiplicative Lattice :=
  (scaleAdd m).toMultiplicative

theorem scaleMul_injective {m : ℕ} (hm : 0 < m) :
    Function.Injective (scaleMul m) := by
  intro v w h
  change v.toAdd = w.toAdd
  change m • v.toAdd = m • w.toAdd at h
  ext i
  have hi := congrFun h i
  simp only [Pi.smul_apply, nsmul_eq_mul] at hi
  have hmz : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
  exact mul_left_cancel₀ hmz hi

theorem scaleMul_commutes_action (m : ℕ) (A : Linear) :
    (scaleMul m).comp (action A).toMonoidHom =
      (action A).toMonoidHom.comp (scaleMul m) := by
  apply MonoidHom.ext
  intro v
  change m • (A • v.toAdd) = A • (m • v.toAdd)
  exact (map_nsmul (DistribMulAction.toAddAut Linear Lattice A).toAdd
    m v.toAdd).symm

/-- The scaling endomorphism `αₘ(v,A)=(mv,A)`. -/
def alpha (m : ℕ) : Gamma →* Gamma :=
  SemidirectProduct.map (scaleMul m) (MonoidHom.id Linear)
    (scaleMul_commutes_action m)

@[simp] theorem alpha_left (m : ℕ) (g : Gamma) :
    (alpha m g).left = scaleMul m g.left := rfl

@[simp] theorem alpha_right (m : ℕ) (g : Gamma) :
    (alpha m g).right = g.right := rfl

theorem alpha_injective {m : ℕ} (hm : 0 < m) :
    Function.Injective (alpha m) := by
  intro g h heq
  apply SemidirectProduct.ext
  · exact scaleMul_injective hm (congrArg SemidirectProduct.left heq)
  · simpa only [alpha_right] using congrArg SemidirectProduct.right heq

/-- Exact image description: the translation coordinate is an `m`-multiple
and the `SL₃(ℤ)` coordinate is unrestricted. -/
theorem mem_range_alpha_iff (m : ℕ) (g : Gamma) :
    g ∈ Set.range (alpha m) ↔
      ∃ v : Lattice, g.left.toAdd = m • v := by
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨h.left.toAdd, rfl⟩
  · rintro ⟨v, hv⟩
    let h : Gamma := ⟨Multiplicative.ofAdd v, g.right⟩
    refine ⟨h, SemidirectProduct.ext ?_ ?_⟩
    · change m • v = g.left.toAdd
      exact hv.symm
    · rfl

/-- For every `m ≥ 2`, the first standard translation does not lie in the
scaled image. -/
theorem a_not_mem_range {m : ℕ} (hm : 2 ≤ m) :
    a ∉ Set.range (alpha m) := by
  rintro ⟨g, hg⟩
  have hleft := congrArg SemidirectProduct.left hg
  change m • g.left.toAdd = aVector at hleft
  have hzero := congrFun hleft 0
  simp only [Pi.smul_apply, nsmul_eq_mul, aVector_zero] at hzero
  have hdvd : (m : ℤ) ∣ 1 := ⟨g.left.toAdd 0, hzero.symm⟩
  have hunit : IsUnit (m : ℤ) := isUnit_iff_dvd_one.mpr hdvd
  rw [Int.isUnit_iff] at hunit
  rcases hunit with hunit | hunit <;> omega

/-- The complete concrete affine-scaling package used by the construction of
the manuscript's family `Eₘ`. -/
theorem scaling_package (m : ℕ) (hm : 2 ≤ m) :
    Function.Injective (alpha m) ∧
      (∀ g : Gamma,
        g ∈ Set.range (alpha m) ↔
          ∃ v : Lattice, g.left.toAdd = m • v) ∧
      a ∉ Set.range (alpha m) :=
  ⟨alpha_injective (by omega), mem_range_alpha_iff m, a_not_mem_range hm⟩

end AffineSL3Scaling
end GroupApproximation
