import GroupApproximation.Manuscript.OneSidedMFRadical.QuantitativeCollapsePerfect

/-!
# Quantitative collapse: from vanishing relation defects to a corona homomorphism

`non_mf_groups_exist.tex`, `prop:linear-collapse`, the analytic half of
step (iv).

A tuple of unitary sequences whose relation defects vanish along the cofinite
filter is exactly a homomorphism of the marked group into the unitary-sequence
corona `NormMatrixCoronaUnitary X`: the free group maps to the product of the
unitary groups, and the relations of `G` land in the null subgroup, so the map
factors through `G`.

The corona is not a countable group, so the printed hypothesis -- every
homomorphism to a *countable* MF group is trivial -- is applied to the image
subgroup, which is countable (a marked group is countable) and MF (it embeds
in the corona by definition).  Triviality of the corona homomorphism is
literally the statement that each generator's unitary sequence converges to
the identity in operator norm.

* `lift_hom_comp`, `lift_pi_apply` — the two evaluation identities for
  `FreeGroup.lift`, both instances of `FreeGroup.lift_unique`.
* `exists_coronaHom` — the factorisation.
* `generators_tendsto_one` — the conclusion actually used by the proof.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical
namespace QuantitativeCollapse

open Filter
open scoped Matrix.Norms.L2Operator

/-! ## Two evaluation identities for the free-group lift -/

/-- A homomorphism applied to the value of a word is the value of the word at
the transported letters. -/
theorem lift_hom_comp {m : ℕ} {H K : Type*} [Group H] [Group K] (φ : H →* K)
    (v : Fin m → H) (r : FreeGroup (Fin m)) :
    φ (FreeGroup.lift v r) = FreeGroup.lift (fun i ↦ φ (v i)) r :=
  FreeGroup.lift_unique (f := fun i ↦ φ (v i)) (φ.comp (FreeGroup.lift v))
    (fun i ↦ by simp) (x := r)

/-- Evaluating a word of unitary sequences at a coordinate is evaluating the
word at that coordinate's unitaries. -/
theorem lift_pi_apply {m : ℕ} (X : ℕ → FiniteModel)
    (u : Fin m → (∀ n, Matrix.unitaryGroup (X n) ℂ)) (r : FreeGroup (Fin m)) (n : ℕ) :
    (FreeGroup.lift u r) n = FreeGroup.lift (fun i ↦ u i n) r :=
  FreeGroup.lift_unique (f := fun i ↦ u i n)
    ((Pi.evalMonoidHom (fun n ↦ Matrix.unitaryGroup (X n) ℂ) n).comp (FreeGroup.lift u))
    (fun i ↦ by simp) (x := r)

/-! ## The factorisation through the marked group -/

/-- **The corona homomorphism.**  A tuple of unitary sequences satisfying every
relation of a marked group modulo null sequences defines a homomorphism of the
group into the unitary-sequence corona, sending each generator to the class of
its sequence. -/
theorem exists_coronaHom {G : Type} [Group G] {m : ℕ} (g : Fin m → G)
    (hgen : Subgroup.closure (Set.range g) = ⊤)
    (X : ℕ → FiniteModel)
    (u : Fin m → (∀ n, Matrix.unitaryGroup (X n) ℂ))
    (hrel : ∀ r : FreeGroup (Fin m), FreeGroup.lift g r = 1 →
      FreeGroup.lift u r ∈ nullCofiniteOpSubgroup X) :
    ∃ θ : G →* NormMatrixCoronaUnitary X,
      ∀ i, θ (g i) = QuotientGroup.mk (u i) := by
  classical
  have hsurj : Function.Surjective (FreeGroup.lift g) := lift_surjective g hgen
  have hinv : Function.RightInverse (Function.surjInv hsurj) (FreeGroup.lift g) :=
    Function.rightInverse_surjInv hsurj
  have hker : (FreeGroup.lift g).ker ≤
      ((QuotientGroup.mk' (nullCofiniteOpSubgroup X)).comp (FreeGroup.lift u)).ker := by
    intro r hr
    rw [MonoidHom.mem_ker] at hr ⊢
    have hnull := hrel r hr
    simpa using (QuotientGroup.eq_one_iff (N := nullCofiniteOpSubgroup X)
      (FreeGroup.lift u r)).mpr hnull
  refine ⟨(FreeGroup.lift g).liftOfRightInverse (Function.surjInv hsurj) hinv
      ⟨(QuotientGroup.mk' (nullCofiniteOpSubgroup X)).comp (FreeGroup.lift u), hker⟩, ?_⟩
  intro i
  have hcomp := MonoidHom.liftOfRightInverse_comp_apply (FreeGroup.lift g)
    (Function.surjInv hsurj) hinv
    ⟨(QuotientGroup.mk' (nullCofiniteOpSubgroup X)).comp (FreeGroup.lift u), hker⟩
    (FreeGroup.of i)
  simpa using hcomp

/-! ## The conclusion drawn from the printed hypothesis -/

/-- **Step (iv), analytic half.**  Let `G` be a marked group whose
homomorphisms into countable MF groups are all trivial.  If a tuple of unitary
sequences over positive-dimensional coordinates satisfies every relation of `G`
asymptotically, then each generator's sequence converges to the identity in
operator norm. -/
theorem generators_tendsto_one
    {G : Type} [Group G] {m : ℕ} (g : Fin m → G)
    (hgen : Subgroup.closure (Set.range g) = ⊤)
    (hkill : ∀ (M : Type) [Group M] [Countable M],
      IsCDEOperatorMF M → ∀ (f : G →* M) (x : G), f x = 1)
    (X : ℕ → FiniteModel) (hX : ∀ n, 0 < Fintype.card (X n))
    (u : Fin m → (∀ n, Matrix.unitaryGroup (X n) ℂ))
    (hrel : ∀ r : FreeGroup (Fin m), FreeGroup.lift g r = 1 →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n in Filter.cofinite,
        opLength (X n) (FreeGroup.lift (fun i ↦ u i n) r) < ε) :
    ∀ i, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in Filter.cofinite, opLength (X n) (u i n) < ε := by
  classical
  haveI : Countable G := countable_of_marked g hgen
  have hrel' : ∀ r : FreeGroup (Fin m), FreeGroup.lift g r = 1 →
      FreeGroup.lift u r ∈ nullCofiniteOpSubgroup X := by
    intro r hr ε hε
    filter_upwards [hrel r hr ε hε] with n hn
    rw [lift_pi_apply]
    exact hn
  obtain ⟨θ, hθ⟩ := exists_coronaHom g hgen X u hrel'
  haveI : Countable θ.range :=
    Function.Surjective.countable θ.rangeRestrict_surjective
  have hMFrange : IsOperatorMF θ.range :=
    ⟨X, hX, θ.range.subtype, fun _ _ h ↦ Subtype.ext h⟩
  have hCDE : IsCDEOperatorMF θ.range :=
    (isCDEOperatorMF_iff_isOperatorMF θ.range).mpr hMFrange
  intro i
  have hone : θ (g i) = 1 := by
    have h1 : θ.rangeRestrict (g i) = 1 := hkill θ.range hCDE θ.rangeRestrict (g i)
    have h2 := congrArg Subtype.val h1
    simpa using h2
  have hmem : u i ∈ nullCofiniteOpSubgroup X := by
    rw [← QuotientGroup.eq_one_iff (N := nullCofiniteOpSubgroup X) (u i)]
    rw [← hθ i]
    exact hone
  exact hmem

end QuantitativeCollapse
end OneSidedMFRadical
end Manuscript
end GroupApproximation
