import GroupApproximation.Manuscript.SimpleKazhdanSofic.HyperbolicKazhdanHost.Admissible
import GroupApproximation.GGT.HullSCUnionGeometryAssembly
import GroupApproximation.Manuscript.NonMF.HullFreeFactorSuitable
import GroupApproximation.Meta.AxiomGuard

/-!
# The start of the Coulon–Fournier-Facio limit: clause G1

`simple_kazhdan_sofic_group.tex`, section "LEF groups", tex l.477–481 (census row
`fc84c012b409`):

> Without LEF, every countable group embeds in a finitely generated simple group~\cite{Gorjuskin,Schupp},
> and even in a simple quotient of a torsion-free hyperbolic Kazhdan group~\cite[Theorem~1.5]{CoulonFournierFacio},
> so one simple Kazhdan group contains Higman's universal finitely presented group~\cite{Higman}.

This module proves clause G1 of `CoulonFournierFacioGeometryStatement`. Let `H` be an infinite,
torsion-free, hyperbolic group with property (T), and let `Γ` be any group. Then `H ∗ Γ` carries
a Hull generating set that contains every letter `inr γ` and over which `inl(H)` is suitable.

## The route

* **The alphabet of `Γ` is all of `Γ`.** Every two vertices of `Γ(Γ, Γ)` are at distance at most
  `1`. So the four-point condition holds with constant `1`
  (`Hyperbolic.isFourPointHyperbolic_of_bounded`). The action is acylindrical vacuously, since
  no two points are `2` apart.
* **The alphabet of `H`.** The Hull generating set of `H` is the one built from a finite
  hyperbolic generating set and two elements without a common power
  (`HullSCUnionGeometry.hullGeneratingSetOfWitness`). Property (T) supplies those two elements
  (`HullSCUnionGeometry.exists_no_common_zpow`).
* **The union alphabet `A_H ⊔ Γ`.**
  * Hyperbolicity: `HullSCUnionGeometry.isFourPointHyperbolic_unionAlphabet`.
  * Acylindricity: the corpus' free-product estimate
    `HullSCUnionGeometry.exists_conjDisplacement_bound`. The assembly
    `isAcylindrical_unionAlphabet_of_isAcylindrical` only needs the two factors to be
    acylindrical, not both to be Hull generating sets.
  * Non-elementarity: `inl` is isometric onto its image (`HullSC.wordDist_inl_eq`).
* **Suitability of `inl(H)`.** Non-elementarity is the image of `H`'s independent loxodromics.
  `H` normalizes no nontrivial finite subgroup, because `H` is infinite and torsion-free
  (`HullFreeFactorSuitable.normalizesNoNontrivialFinite_range_inl`).
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic
namespace HyperbolicKazhdanHost

open Monoid Monoid.CoprodI
open GroupApproximation.WordMetric
open GroupApproximation.HullGeometry
open GroupApproximation.FreeProductCyclic
open GroupApproximation.FreeProductUnionNorm
open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.HullSCUnionGeometry

/-! ## The whole group as an alphabet -/

/-- The alphabet consisting of every element of `Γ`. -/
def univAlphabet (Γ : Type) [Group Γ] : Alphabet Γ :=
  ⟨Set.univ, ⟨fun x _ => Set.mem_univ x⁻¹, Subgroup.closure_univ⟩⟩

#audit_axioms GroupApproximation.SimpleKazhdanSofic.HyperbolicKazhdanHost.univAlphabet

/-- Over the whole group, any two elements are at word distance at most `1`. -/
theorem wordDist_univAlphabet_le_one (Γ : Type) [Group Γ] (x y : Γ) :
    wordDist (univAlphabet Γ).carrier x y ≤ 1 := by
  show wordNorm (univAlphabet Γ).carrier (x⁻¹ * y) ≤ 1
  exact wordNorm_le_one_of_mem (S := (univAlphabet Γ).carrier) (Set.mem_univ (x⁻¹ * y))

#audit_axioms GroupApproximation.SimpleKazhdanSofic.HyperbolicKazhdanHost.wordDist_univAlphabet_le_one

/-- `Γ(Γ, Γ)` is four-point hyperbolic with constant `1`. -/
theorem isFourPointHyperbolic_univAlphabet (Γ : Type) [Group Γ] :
    Hyperbolic.IsFourPointHyperbolic (univAlphabet Γ).carrier 1 :=
  Hyperbolic.isFourPointHyperbolic_of_bounded (wordDist_univAlphabet_le_one Γ)

#audit_axioms GroupApproximation.SimpleKazhdanSofic.HyperbolicKazhdanHost.isFourPointHyperbolic_univAlphabet

/-- The translation action on `Γ(Γ, Γ)` is acylindrical, vacuously: no two vertices are `2`
apart. -/
theorem isAcylindrical_univAlphabet (Γ : Type) [Group Γ] :
    IsAcylindrical Γ (Cayley (univAlphabet Γ)) := by
  intro _ _
  refine ⟨2, 0, ?_⟩
  intro x y hxy
  exfalso
  have hle : dist x y ≤ 1 := by
    rw [Cayley.dist_eq]
    exact_mod_cast wordDist_univAlphabet_le_one Γ (Cayley.val x) (Cayley.val y)
  linarith

#audit_axioms GroupApproximation.SimpleKazhdanSofic.HyperbolicKazhdanHost.isAcylindrical_univAlphabet

/-! ## Acylindricity of the union alphabet, from acylindricity of the factors -/

section Union

variable {E H : Type} [Group E] [Group H]

/-- **The two factors' displacement bounds, made uniform.** This is the statement of
`HullSCUnionGeometry.exists_famDisplacement_bound`, but it only assumes the two factor actions
are acylindrical. -/
theorem exists_famDisplacement_bound_of_isAcylindrical (A : Alphabet E) (B : Alphabet H)
    (hA : IsAcylindrical E (Cayley A)) (hB : IsAcylindrical H (Cayley B))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (R₀ : ℝ) (N₀ : ℕ), ∀ (i : Bool) (τ : Higman.Amalgam.fam E H i),
      R₀ ≤ ((wordNorm (famCarrier A.carrier B.carrier i) τ : ℕ) : ℝ) →
        {γ : Higman.Amalgam.fam E H i |
            ((wordNorm (famCarrier A.carrier B.carrier i) γ : ℕ) : ℝ) ≤ ε ∧
            ((wordNorm (famCarrier A.carrier B.carrier i)
              (τ⁻¹ * γ * τ) : ℕ) : ℝ) ≤ ε}.Finite ∧
          {γ : Higman.Amalgam.fam E H i |
            ((wordNorm (famCarrier A.carrier B.carrier i) γ : ℕ) : ℝ) ≤ ε ∧
            ((wordNorm (famCarrier A.carrier B.carrier i)
              (τ⁻¹ * γ * τ) : ℕ) : ℝ) ≤ ε}.ncard ≤ N₀ := by
  obtain ⟨RE, NE, hE⟩ := exists_factorDisplacement_bound A hA hε
  obtain ⟨RH, NH, hH⟩ := exists_factorDisplacement_bound B hB hε
  refine ⟨max RE RH, max NE NH, ?_⟩
  intro i
  cases i with
  | false =>
      intro τ hτ
      obtain ⟨hfin, hcard⟩ := hE τ (le_trans (le_max_left _ _) hτ)
      exact ⟨hfin, le_trans hcard (le_max_left _ _)⟩
  | true =>
      intro τ hτ
      obtain ⟨hfin, hcard⟩ := hH τ (le_trans (le_max_right _ _) hτ)
      exact ⟨hfin, le_trans hcard (le_max_right _ _)⟩

#audit_axioms GroupApproximation.SimpleKazhdanSofic.HyperbolicKazhdanHost.exists_famDisplacement_bound_of_isAcylindrical

/-- **The translation action of `E ∗ H` on the union alphabet is acylindrical** once the two
factor actions are. The argument is that of `HullSCUnionGeometry.isAcylindrical_unionAlphabet`:
move the free-product estimate `exists_conjDisplacement_bound` along `Higman.coprodEquiv`. -/
theorem isAcylindrical_unionAlphabet_of_isAcylindrical (A : Alphabet E) (B : Alphabet H)
    (hA : IsAcylindrical E (Cayley A)) (hB : IsAcylindrical H (Cayley B)) :
    IsAcylindrical (Monoid.Coprod E H) (Cayley (HullSC.unionAlphabet A B)) := by
  classical
  letI : ∀ b : Bool, DecidableEq (Higman.Amalgam.fam E H b) :=
    fun b => Classical.decEq (Higman.Amalgam.fam E H b)
  refine isAcylindrical_cayley_of_conjDisplacement _ ?_
  intro ε hε
  have hfam : ∀ b : Bool, IsSymmetricGeneratingSet (famCarrier A.carrier B.carrier b) :=
    isSymmetricGeneratingSet_famCarrier A.symmetricGenerating B.symmetricGenerating
  -- the union alphabet, read on `CoprodI (Amalgam.fam E H)`
  let A' : Alphabet (CoprodI (Higman.Amalgam.fam E H)) :=
    ⟨unionCarrier (famCarrier A.carrier B.carrier), isSymmetricGeneratingSet_unionCarrier hfam⟩
  -- the isomorphism preserves word length
  have hmem : ∀ x ∈ HullSC.UnionCarrier A B,
      Higman.coprodEquiv x ∈ unionCarrier (famCarrier A.carrier B.carrier) := by
    intro x hx
    rcases HullSC.mem_unionCarrier.mp hx with ⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩
    · exact ⟨false, a, ha, (coprodEquiv_inl a).symm⟩
    · exact ⟨true, b, hb, (coprodEquiv_inr b).symm⟩
  have hmem' : ∀ x ∈ unionCarrier (famCarrier A.carrier B.carrier),
      Higman.coprodEquiv.symm x ∈ HullSC.UnionCarrier A B := by
    rintro x ⟨i, a, ha, rfl⟩
    cases i with
    | false =>
        exact HullSC.mem_unionCarrier.mpr
          (Or.inl ⟨a, ha, (coprodEquiv_symm_false a).symm⟩)
    | true =>
        exact HullSC.mem_unionCarrier.mpr
          (Or.inr ⟨a, ha, (coprodEquiv_symm_true a).symm⟩)
  have hnorm : ∀ w : Monoid.Coprod E H,
      wordNorm (unionCarrier (famCarrier A.carrier B.carrier)) (Higman.coprodEquiv w)
        = wordNorm (HullSC.UnionCarrier A B) w :=
    HullSC.wordNorm_of_mulEquiv
      (HullSC.unionAlphabet A B).symmetricGenerating
      (isSymmetricGeneratingSet_unionCarrier hfam)
      (Higman.coprodEquiv (G := E) (H := H)) hmem hmem'
  obtain ⟨R₀, N₀, hfac⟩ := exists_famDisplacement_bound_of_isAcylindrical A B hA hB hε
  obtain ⟨R, N, hRN⟩ :=
    exists_conjDisplacement_bound hfam (A := A') rfl hε hfac
  refine ⟨R, N, ?_⟩
  intro t hRt
  have hRt' : R ≤ ((wordNorm (unionCarrier (famCarrier A.carrier B.carrier))
      (Higman.coprodEquiv t) : ℕ) : ℝ) := by
    rw [hnorm t]
    exact hRt
  obtain ⟨hfin, hcard⟩ := hRN (Higman.coprodEquiv t) hRt'
  -- the two displacement sets correspond
  have hmemD : ∀ k : Monoid.Coprod E H,
      k ∈ conjDisplacement (HullSC.unionAlphabet A B) ε t
        ↔ Higman.coprodEquiv k ∈ conjDisplacement A' ε (Higman.coprodEquiv t) := by
    intro k
    have hmap : Higman.coprodEquiv (t⁻¹ * k * t)
        = (Higman.coprodEquiv t)⁻¹ * Higman.coprodEquiv k * Higman.coprodEquiv t := by
      rw [map_mul, map_mul, map_inv]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · show ((wordNorm (unionCarrier (famCarrier A.carrier B.carrier))
            (Higman.coprodEquiv k) : ℕ) : ℝ) ≤ ε
        rw [hnorm k]
        exact h1
      · show ((wordNorm (unionCarrier (famCarrier A.carrier B.carrier))
            ((Higman.coprodEquiv t)⁻¹ * Higman.coprodEquiv k
              * Higman.coprodEquiv t) : ℕ) : ℝ) ≤ ε
        rw [← hmap, hnorm (t⁻¹ * k * t)]
        exact h2
    · rintro ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · show ((wordNorm (HullSC.UnionCarrier A B) k : ℕ) : ℝ) ≤ ε
        rw [← hnorm k]
        exact h1
      · show ((wordNorm (HullSC.UnionCarrier A B) (t⁻¹ * k * t) : ℕ) : ℝ) ≤ ε
        rw [← hnorm (t⁻¹ * k * t), hmap]
        exact h2
  have hseteq : conjDisplacement (HullSC.unionAlphabet A B) ε t
      = (fun x => Higman.coprodEquiv.symm x) ''
        conjDisplacement A' ε (Higman.coprodEquiv t) := by
    ext k
    constructor
    · intro hk
      exact ⟨Higman.coprodEquiv k, (hmemD k).mp hk, Higman.coprodEquiv.symm_apply_apply k⟩
    · rintro ⟨x, hx, rfl⟩
      refine (hmemD _).mpr ?_
      rwa [Higman.coprodEquiv.apply_symm_apply]
  rw [hseteq]
  refine ⟨hfin.image _, ?_⟩
  rw [Set.ncard_image_of_injective _ Higman.coprodEquiv.symm.injective]
  exact hcard

#audit_axioms GroupApproximation.SimpleKazhdanSofic.HyperbolicKazhdanHost.isAcylindrical_unionAlphabet_of_isAcylindrical

end Union

/-! ## Clause G1 -/

/-- **Clause G1 of `CoulonFournierFacioGeometryStatement`.** Let `H` be an infinite,
torsion-free, hyperbolic group with property (T), and let `Γ` be any group. Then `H ∗ Γ` has a
Hull generating set containing every letter `inr γ`, and `inl(H)` is suitable over it. -/
theorem coulonFournierFacioGeometry_start (H Γ : Type) [Group H] [Group Γ]
    (hinf : Infinite H) (htf : IsPowerTorsionFree H)
    (hhyp : Hyperbolic.IsHyperbolicGroup H) (hKT : HasKazhdanPropertyT.{0, 0} H) :
    ∃ A : HullGeneratingSet (Monoid.Coprod H Γ),
      (∀ γ : Γ, (Monoid.Coprod.inr γ : Monoid.Coprod H Γ) ∈ A.alphabet.carrier) ∧
        Suitable A.alphabet (Monoid.Coprod.inl : H →* Monoid.Coprod H Γ).range := by
  obtain ⟨g, hg⟩ := exists_not_isOfFinOrder_of_infinite hinf htf
  obtain ⟨t, ht1, hnc⟩ := exists_no_common_zpow hinf hhyp hKT hg
  obtain ⟨T, hTsym, δ, hδ⟩ := hhyp
  obtain ⟨B⟩ : Nonempty (HullGeneratingSet H) :=
    ⟨hullGeneratingSetOfWitness hTsym hδ hg
      (notMem_elementaryClosure_of_no_common_zpow (⟨(T : Set H), hTsym⟩ : Alphabet H)
        T.finite_toSet (GGT.isHyperbolicSpace_cayley_of_fourPoint _ hδ) htf hg hnc ht1)⟩
  have hcar : (HullSC.unionAlphabet B.alphabet (univAlphabet Γ)).carrier
      = HullSC.UnionCarrier B.alphabet (univAlphabet Γ) := rfl
  have hfourB : Hyperbolic.IsFourPointHyperbolic B.alphabet.carrier (max ⌈B.delta⌉₊ 1) :=
    (isFourPointHyperbolic_of_isHyperbolicSpace B.alphabet B.hyperbolic).mono
      (le_max_left _ _)
  have hfourΓ : Hyperbolic.IsFourPointHyperbolic (univAlphabet Γ).carrier
      (max ⌈B.delta⌉₊ 1) :=
    (isFourPointHyperbolic_univAlphabet Γ).mono (le_max_right _ _)
  have hne : ActsNonElementarily (Monoid.Coprod.inl : H →* Monoid.Coprod H Γ).range
      (Cayley.base (HullSC.unionAlphabet B.alphabet (univAlphabet Γ))) :=
    HullSC.actsNonElementarily_range_of_wordDist_eq
      (Monoid.Coprod.inl : H →* Monoid.Coprod H Γ) (HullSC.wordDist_inl_eq hcar)
      B.nonElementary
  refine ⟨⟨HullSC.unionAlphabet B.alphabet (univAlphabet Γ), ((max ⌈B.delta⌉₊ 1 : ℕ) : ℝ),
    GGT.isHyperbolicSpace_cayley_of_fourPoint _
      (isFourPointHyperbolic_unionAlphabet _ _ hfourB hfourΓ),
    isAcylindrical_unionAlphabet_of_isAcylindrical B.alphabet (univAlphabet Γ)
      B.acylindrical (isAcylindrical_univAlphabet Γ),
    HullSC.actsNonElementarily_top_of_subgroup hne⟩, ?_, ?_⟩
  · intro γ
    exact (HullSC.mem_unionCarrier (A := B.alphabet) (B := univAlphabet Γ)).mpr
      (Or.inr ⟨γ, Set.mem_univ γ, rfl⟩)
  · haveI := hinf
    exact ⟨hne, Manuscript.NonMF.HullFreeFactorSuitable.normalizesNoNontrivialFinite_range_inl
      (Manuscript.NonMF.TorsionFreePrinted.hasTrivialFiniteRadical_of_torsionFree htf)⟩

#audit_axioms GroupApproximation.SimpleKazhdanSofic.HyperbolicKazhdanHost.coulonFournierFacioGeometry_start

end HyperbolicKazhdanHost
end SimpleKazhdanSofic
end GroupApproximation
