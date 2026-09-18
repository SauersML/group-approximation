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

