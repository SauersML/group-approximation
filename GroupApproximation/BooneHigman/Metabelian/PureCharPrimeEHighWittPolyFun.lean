import GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEHighWittPoly
import GroupApproximation.Meta.AxiomGuard

/-!
# The weighted polynomial space is invariant, finite-dimensional and separating
(bh-met-87c, part 4)

For the space `eHighWitt_polySpace w co d` of `PureCharPrimeEHighWittPoly`:

* `eHighWitt_polySpace_comp`: it is stable under precomposition with any weight-polynomial
  map;
* `eHighWitt_polySpace_finite`: it is finite-dimensional when `σ` is finite and all weights
  are positive;
* `eHighWitt_polySpace_sep`: it separates points whose coordinates differ, provided every
  weight is `≤ d`.

`eHighWitt_exists_polyFun_of_weightPoly` packages these three facts in the shape used by
`EHighArtinHassePolyFunStatement`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Coprimary

open MvPolynomial

noncomputable section

variable {L : Type} [Field L] {σ : Type}

/-- Stability of the weighted polynomial space under weight-polynomial maps. -/
theorem eHighWitt_polySpace_comp {N : Type} {w : σ → ℕ} {co : N → σ → L} {g : N → N}
    (hg : eHighWitt_IsWeightPoly w co g) (d : ℕ) {f : N → L}
    (hf : f ∈ eHighWitt_polySpace w co d) :
    (fun x => f (g x)) ∈ eHighWitt_polySpace w co d := by
  unfold eHighWitt_IsWeightPoly at hg
  choose Φ hΦ hΦx using hg
  obtain ⟨P, hP, rfl⟩ := Submodule.mem_map.mp hf
  let ψ : Option σ → MvPolynomial (Option σ) L := fun o => Option.elim o (X none) Φ
  have hψ : ∀ o, IsWeightedHomogeneous (eHighWitt_hwt w) (ψ o) (eHighWitt_hwt w o) := by
    intro o
    cases o with
    | none => exact isWeightedHomogeneous_X L _ none
    | some v => exact hΦ v
  have hfun : ∀ x, (fun o => aeval (eHighWitt_hpt (co x)) (ψ o)) = eHighWitt_hpt (co (g x)) := by
    intro x
    funext o
    cases o with
    | none => exact aeval_X (eHighWitt_hpt (co x)) none
    | some v => exact (hΦx v x).symm
  have hP' : IsWeightedHomogeneous (eHighWitt_hwt w) P d :=
    (mem_weightedHomogeneousSubmodule L _ _ _).mp hP
  refine Submodule.mem_map.mpr ⟨bind₁ ψ P, (mem_weightedHomogeneousSubmodule L _ _ _).mpr
    (eHighWitt_isWH_bind₁ ψ hψ hP'), ?_⟩
  funext x
  show aeval (eHighWitt_hpt (co x)) (bind₁ ψ P) = aeval (eHighWitt_hpt (co (g x))) P
  exact (aeval_bind₁ _ _ _).trans
    (congrArg (fun F : Option σ → L => aeval F P) (hfun x))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWitt_polySpace_comp

/-- Finite-dimensionality of the weighted polynomial space. -/
theorem eHighWitt_polySpace_finite [Fintype σ] {N : Type} (w : σ → ℕ) (hw : ∀ v, w v ≠ 0)
    (co : N → σ → L) (d : ℕ) : FiniteDimensional L (eHighWitt_polySpace w co d) := by
  have hw' : ∀ o : Option σ, eHighWitt_hwt w o ≠ 0 := by
    intro o
    cases o with
    | none => exact Nat.one_ne_zero
    | some v => exact hw v
  exact Module.Finite.iff_fg.mpr ((weightedHomogeneousSubmodule_fg L _ hw' d).map _)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWitt_polySpace_finite

/-- The weighted polynomial space separates points with different coordinates. -/
theorem eHighWitt_polySpace_sep {N : Type} (w : σ → ℕ) (co : N → σ → L) (d : ℕ)
    (hwd : ∀ v, w v ≤ d) {x y : N} (hxy : co x ≠ co y) :
    ∃ f ∈ eHighWitt_polySpace w co d, f x ≠ f y := by
  obtain ⟨v, hv⟩ := Function.ne_iff.mp hxy
  refine ⟨eHighWitt_evalMap co (X (some v) * X none ^ (d - w v)),
    Submodule.mem_map_of_mem ?_, ?_⟩
  · rw [mem_weightedHomogeneousSubmodule]
    refine eHighWitt_isWH_of_eq ((isWeightedHomogeneous_X L _ (some v)).mul
      (eHighWitt_isWH_X_pow w none (d - w v))) ?_
    show w v + 1 * (d - w v) = d
    have hv' := hwd v
    omega
  · simp only [eHighWitt_evalMap_apply, map_mul, map_pow, aeval_X]
    show co x v * 1 ^ (d - w v) ≠ co y v * 1 ^ (d - w v)
    rwa [one_pow, mul_one, mul_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWitt_polySpace_sep

/-- A finite-dimensional, translation-stable, `act`-stable, separating space of functions on
`N`, provided translations and every `act q` are weight-polynomial for injective coordinates. -/
theorem eHighWitt_exists_polyFun_of_weightPoly [Fintype σ] {N Q : Type} [AddCommGroup N]
    (w : σ → ℕ) (hw : ∀ v, w v ≠ 0) (d : ℕ) (hwd : ∀ v, w v ≤ d) (co : N → σ → L)
    (hco : Function.Injective co) (act : Q → N → N)
    (htrans : ∀ m : N, eHighWitt_IsWeightPoly w co (· + m))
    (hact : ∀ q : Q, eHighWitt_IsWeightPoly w co (act q)) :
    ∃ V : Submodule L (N → L), FiniteDimensional L V ∧
      (∀ m : N, ∀ f ∈ V, (fun x => f (x + m)) ∈ V) ∧
      (∀ q : Q, ∀ f ∈ V, (fun x => f (act q x)) ∈ V) ∧
      (∀ m : N, m ≠ 0 → ∃ f ∈ V, f m ≠ f 0) :=
  ⟨eHighWitt_polySpace w co d, eHighWitt_polySpace_finite w hw co d,
    fun m _ hf => eHighWitt_polySpace_comp (htrans m) d hf,
    fun q _ hf => eHighWitt_polySpace_comp (hact q) d hf,
    fun _ hm => eHighWitt_polySpace_sep w co d hwd fun h => hm (hco h)⟩

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWitt_exists_polyFun_of_weightPoly

end

end GroupApproximation.BooneHigman.Metabelian.Coprimary
