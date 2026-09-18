import GroupApproximation.Algebra.FinitePresentationTietze
import Mathlib.GroupTheory.QuotientGroup.Defs
import GroupApproximation.Meta.AxiomGuard

/-!
# A finite presentation gives a unital section on every finite generating family

The section statements of `EnvelopeHigmanVSection.lean` and `EnvelopeHigmanVSwapGenReduce.lean`
ask, for a finite family `g : Fin n → G` generating `G`, for
* a finite set `R ⊆ ker (FreeGroup.lift g)` of relators, and
* a map `s : G → FreeGroup (Fin n) ⧸ ⟨⟨R⟩⟩` with `s 1 = 1` and `s v * of i = s (v * g i)`.

This module proves that this follows from the bare finite presentability of `G`.
* `higmanVPresent_section`: if `φ : K →* H` is surjective and `ker φ ≤ N` for a normal `N`,
  then `s h := surjInv φ h` (mod `N`) sends `1` to `1` and intertwines right multiplication:
  two elements of `K` with the same image under `φ` are congruent mod `N`.
* `higmanVPresent_section_of_fp`: if `G` is finitely presented and `g` generates `G`, then
  `FreeGroup.lift g` is surjective, its kernel is the normal closure of a finite set `R` by the
  Tietze step `Tietze.isFinitelyNormallyGenerated_ker` (B. H. Neumann: the kernel of *every*
  surjection from a free group of finite rank onto a finitely presented group is finitely
  normally generated), and `higmanVPresent_section` with `N = ⟨⟨R⟩⟩` gives the section.

Nothing here is specific to `V_d`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- **Section from a kernel bound.**  If `φ : K →* H` is surjective and `ker φ ≤ N` for a normal
subgroup `N`, then some map `s : H → K ⧸ N` sends `1` to `1` and intertwines right multiplication
by `k` with right multiplication by `φ k`. -/
theorem higmanVPresent_section {K H : Type*} [Group K] [Group H] (φ : K →* H)
    (hφ : Function.Surjective φ) (N : Subgroup K) [N.Normal] (hN : φ.ker ≤ N) :
    ∃ s : H → K ⧸ N, s 1 = 1 ∧ ∀ (h : H) (k : K), s h * (k : K ⧸ N) = s (h * φ k) := by
  have key : ∀ a b : K, φ a = φ b → (a : K ⧸ N) = b := by
    intro a b hab
    refine QuotientGroup.eq.mpr (hN ?_)
    rw [MonoidHom.mem_ker, map_mul, map_inv, hab, inv_mul_cancel]
  refine ⟨fun h => ((Function.surjInv hφ h : K) : K ⧸ N), ?_, fun h k => ?_⟩
  · show ((Function.surjInv hφ 1 : K) : K ⧸ N) = 1
    exact (key _ 1 (by rw [Function.surjInv_eq hφ 1, map_one])).trans (QuotientGroup.mk_one N)
  · show ((Function.surjInv hφ h : K) : K ⧸ N) * (k : K ⧸ N) =
      ((Function.surjInv hφ (h * φ k) : K) : K ⧸ N)
    rw [← QuotientGroup.mk_mul]
    exact key _ _ (by rw [map_mul, Function.surjInv_eq hφ h, Function.surjInv_eq hφ (h * φ k)])

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVPresent_section

/-- **Finite presentation gives the section on every finite generating family.**  If `G` is
finitely presented and `g : Fin n → G` generates `G`, then finitely many relators in the kernel
of `FreeGroup.lift g` carry a unital section intertwining right multiplication by the letters with
right multiplication by the generators. -/
theorem higmanVPresent_section_of_fp {G : Type*} [Group G] [Group.IsFinitelyPresented G]
    {n : ℕ} (g : Fin n → G) (hg : Subgroup.closure (Set.range g) = ⊤) :
    ∃ R : Set (FreeGroup (Fin n)), R.Finite ∧ R ⊆ (FreeGroup.lift g).ker ∧
      ∃ s : G → FreeGroup (Fin n) ⧸ Subgroup.normalClosure R,
        s 1 = 1 ∧
          ∀ (v : G) (i : Fin n),
            s v * ((FreeGroup.of i : FreeGroup (Fin n)) :
              FreeGroup (Fin n) ⧸ Subgroup.normalClosure R) = s (v * g i) := by
  have hsurj : Function.Surjective (FreeGroup.lift g) := by
    rw [← MonoidHom.range_eq_top, FreeGroup.range_lift_eq_closure]
    exact hg
  obtain ⟨R, hR, hRker⟩ := Tietze.isFinitelyNormallyGenerated_ker (FreeGroup.lift g) hsurj
  obtain ⟨s, hs1, hmul⟩ :=
    higmanVPresent_section (FreeGroup.lift g) hsurj (Subgroup.normalClosure R) hRker.symm.le
  refine ⟨R, hR, ?_, s, hs1, fun v i => ?_⟩
  · rw [← hRker]
    exact Subgroup.subset_normalClosure
  · rw [hmul v (FreeGroup.of i), FreeGroup.lift_apply_of]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVPresent_section_of_fp

end GroupApproximation.BooneHigman.Metabelian.Envelope
