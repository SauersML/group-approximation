import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.Finset.NAry
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.RingTheory.Finiteness.Basic
import GroupApproximation.Meta.AxiomGuard

/-!
# Finiteness of a Frobenius-twisted module (lane bh-met-52)

Let `Q` be a finitely generated commutative group, `k` a commutative ring with `c ^ n = c` for all
`c : k` (e.g. `k = ZMod p`, `n = p ^ e`), and `N` a finitely generated `k[Q]`-module.  Suppose a
ring `D` acts on `N` through a surjection `π : k[Q] → D` twisted by the `n`-th power map:
`π r • y = r ^ n • y`.  Then `N` is a finitely generated `D`-module.

Proof.  `Q ⧸ Q^n` is a finitely generated torsion commutative group, hence finite, so there is a
finite `s ⊆ Q` with `Q = s · Q^n` (`exists_finset_pow_cover`).  If `G` generates `N` over
`k[Q]`, the `D`-span `W` of `{q₀ • g | q₀ ∈ s, g ∈ G}` contains `q • g` for all `q ∈ Q`
(write `q = q₀ u^n`, and `u^n` acts as `π u`), is stable under `Q` and under `k`
(since `c = c ^ n`), hence under `k[Q]`, so it contains the `k[Q]`-span of `G`, which is `N`.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Coprimary

/-- In a finitely generated commutative group, finitely many elements represent all cosets of the
subgroup of `n`-th powers. -/
theorem exists_finset_pow_cover {Q : Type} [CommGroup Q] [Group.FG Q] {n : ℕ} (hn : 0 < n) :
    ∃ s : Finset Q, ∀ q : Q, ∃ q₀ ∈ s, ∃ u : Q, q = q₀ * u ^ n := by
  let U : Subgroup Q := (powMonoidHom n : Q →* Q).range
  haveI : U.Normal := ⟨fun a ha g => by rwa [mul_comm g a, mul_inv_cancel_right]⟩
  haveI : Group.FG (Q ⧸ U) := Group.fg_of_surjective (QuotientGroup.mk'_surjective U)
  haveI : Finite (Q ⧸ U) := CommGroup.finite_of_fg_torsion fun x => by
    induction x using QuotientGroup.induction_on with
    | H z =>
      refine isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact MonoidHom.mem_range.mpr ⟨z, rfl⟩
  haveI : Fintype (Q ⧸ U) := Fintype.ofFinite _
  classical
  refine ⟨Finset.univ.image fun x : Q ⧸ U => x.out, fun q => ?_⟩
  obtain ⟨⟨h, hh⟩, hq⟩ := QuotientGroup.mk_out_eq_mul U q
  obtain ⟨u, hu⟩ := MonoidHom.mem_range.mp hh
  have hu' : ((⟨h, hh⟩ : U) : Q) = u ^ n := hu.symm
  refine ⟨(QuotientGroup.mk q : Q ⧸ U).out, Finset.mem_image_of_mem _ (Finset.mem_univ _), u⁻¹,
    ?_⟩
  rw [hq, hu', inv_pow, mul_inv_cancel_right]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.exists_finset_pow_cover

/-- **Finiteness of a Frobenius-twisted module.**  If a finitely generated `k[Q]`-module `N`
(with `Q` finitely generated commutative and `c ^ n = c` on `k`) carries a `D`-module structure
through a surjection `π : k[Q] → D` with `π r • y = r ^ n • y`, then `N` is finite over `D`. -/
theorem twist_finite {k Q N D : Type} [CommRing k] [CommGroup Q] [Group.FG Q] [AddCommGroup N]
    [Module (MonoidAlgebra k Q) N] [Module.Finite (MonoidAlgebra k Q) N] [CommRing D]
    [Module D N] (π : MonoidAlgebra k Q →+* D) (hπ : Function.Surjective π) {n : ℕ} (hn : 0 < n)
    (hk : ∀ c : k, c ^ n = c)
    (hsmul : ∀ (r : MonoidAlgebra k Q) (y : N), π r • y = r ^ n • y) :
    Module.Finite D N := by
  classical
  obtain ⟨s, hs⟩ := exists_finset_pow_cover (Q := Q) hn
  obtain ⟨G, hG⟩ := (Module.Finite.fg_top : (⊤ : Submodule (MonoidAlgebra k Q) N).FG)
  obtain ⟨X, hX⟩ : ∃ X : Finset N,
      X = Finset.image₂ (fun q g => MonoidAlgebra.of k Q q • g) s G := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W : Submodule D N, W = Submodule.span D (X : Set N) := ⟨_, rfl⟩
  have hpow : ∀ (r : MonoidAlgebra k Q) (y : N), y ∈ W → r ^ n • y ∈ W := fun r y hy => by
    rw [← hsmul]
    exact W.smul_mem _ hy
  have hcomm : ∀ (q : Q) (a : D) (y : N),
      MonoidAlgebra.of k Q q • a • y = a • MonoidAlgebra.of k Q q • y := by
    intro q a y
    obtain ⟨r, rfl⟩ := hπ a
    rw [hsmul, hsmul, smul_smul, smul_smul, mul_comm (MonoidAlgebra.of k Q q)]
  have hgen : ∀ (q : Q) (g : N), g ∈ G → MonoidAlgebra.of k Q q • g ∈ W := by
    intro q g hg
    obtain ⟨q₀, hq₀, u, rfl⟩ := hs q
    rw [map_mul (MonoidAlgebra.of k Q), map_pow (MonoidAlgebra.of k Q),
      mul_comm (MonoidAlgebra.of k Q q₀), mul_smul]
    refine hpow _ _ ?_
    rw [hW]
    exact Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_image₂_of_mem hq₀ hg))
  have hof : ∀ (q : Q) (y : N), y ∈ W → MonoidAlgebra.of k Q q • y ∈ W := by
    intro q y hy
    rw [hW] at hy ⊢
    induction hy using Submodule.span_induction with
    | mem x hx =>
      rw [Finset.mem_coe, hX, Finset.mem_image₂] at hx
      obtain ⟨q₀, _, g, hg, rfl⟩ := hx
      rw [smul_smul, ← map_mul (MonoidAlgebra.of k Q), ← hW]
      exact hgen _ g hg
    | zero =>
      rw [smul_zero]
      exact Submodule.zero_mem _
    | add x x' _ _ hx hx' =>
      rw [smul_add]
      exact Submodule.add_mem _ hx hx'
    | smul a x _ hx =>
      rw [hcomm]
      exact Submodule.smul_mem _ a hx
  have hR : ∀ (r : MonoidAlgebra k Q) (y : N), y ∈ W → r • y ∈ W := by
    intro r
    refine MonoidAlgebra.induction_on (p := fun r => ∀ y : N, y ∈ W → r • y ∈ W) r
      (fun q => hof q) (fun x x' hx hx' y hy => ?_) (fun c x hx y hy => ?_)
    · rw [add_smul]
      exact W.add_mem (hx y hy) (hx' y hy)
    · rw [Algebra.smul_def, mul_smul, ← hk c, map_pow]
      exact hpow _ _ (hx y hy)
  have htop : ∀ y : N, y ∈ W := by
    intro y
    have hy : y ∈ (⊤ : Submodule (MonoidAlgebra k Q) N) := Submodule.mem_top
    rw [← hG] at hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      simpa only [map_one, one_smul] using hgen 1 x (Finset.mem_coe.mp hx)
    | zero => exact W.zero_mem
    | add x x' _ _ hx hx' => exact W.add_mem hx hx'
    | smul r x _ hx => exact hR r x hx
  exact ⟨⟨X, by rw [← hW]; exact eq_top_iff.mpr fun y _ => htop y⟩⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.twist_finite

end Coprimary
end Metabelian
end BooneHigman
end GroupApproximation
