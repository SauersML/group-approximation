import GroupApproximation.GGT.OsinTheorem54SepSymmetric
import GroupApproximation.GGT.OsinTheorem54SepFiniteFam

/-!
# Symmetrising the base, at a general family

The general-`Λ` form of `GGT/OsinTheorem54SepSymmetric.lean`.

Only one step of that argument is sensitive to the number of peripheral
subgroups.  The letters at which reversal bites are the `x ∈ X` with
`x⁻¹ ∉ X`, and each of them lies in `X ∩ H_λ` for *some* `λ`; each such
intersection is finite by `finite_base_inter_fam`, with no hypothesis at all,
but their union is finite only when there are finitely many of them.  So
`finite_base_asymmetry'` and `exists_symmetric_base'` carry `[Finite Λ]`, and
nothing else here does.

The rest transports verbatim.  The symmetrisation has the *same alphabet*
(`alphabet_eq_of_symmetrizedBase'`), so clause (a) of `↪_h` is literally the
same statement for the two relative generating sets; and clause (b) is
`relBall_finite_of_base_subset'`, which runs one `λ` at a time and needs no
hypothesis on `Λ` at all.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- **The letters whose inverse is not a letter form a finite set**, for a
finite family.

Each of them lies in `X ∩ H_λ` for some `λ`, and each `X ∩ H_λ` is finite by
`finite_base_inter_fam`; finiteness of the union is where `[Finite Λ]` enters,
and it is the only place in this file where it does. -/
theorem finite_base_asymmetry' [Finite Λ] (D : RelGenSet G Λ)
    (hemb : D.IsHyperbolicallyEmbedded) :
    {y : G | y ∈ D.base ∧ y⁻¹ ∉ D.base}.Finite := by
  refine (Set.finite_iUnion (fun lam : Λ =>
    finite_base_inter_fam D hemb lam)).subset ?_
  rintro y ⟨hyb, hyn⟩
  have hyA : y ∈ D.alphabet.carrier := Set.mem_union_left _ hyb
  have hinvA : y⁻¹ ∈ D.base ∪ (⋃ lam : Λ, ((D.fam lam : Subgroup G) : Set G)) :=
    D.symmetricGenerating.inv_mem y hyA
  rcases hinvA with hbase | hfam
  · exact absurd hbase hyn
  · obtain ⟨lam, hlam⟩ := Set.mem_iUnion.mp hfam
    have hlam' : y⁻¹ ∈ D.fam lam := hlam
    have hinv := inv_mem hlam'
    rw [inv_inv] at hinv
    refine Set.mem_iUnion.mpr ⟨lam, ?_⟩
    exact ⟨hyb, hinv⟩

/-- **Symmetrising the base does not enlarge the alphabet**, at a general
family. -/
theorem symmetrizedBase_subset_alphabet' (D : RelGenSet G Λ) :
    {x : G | x ∈ D.base ∨ x⁻¹ ∈ D.base} ⊆ D.alphabet.carrier := by
  rintro x (hx | hx)
  · exact Set.mem_union_left _ hx
  · have hxinv : x⁻¹ ∈ D.alphabet.carrier := Set.mem_union_left _ hx
    have h := D.symmetricGenerating.inv_mem x⁻¹ hxinv
    rwa [inv_inv] at h

/-- **The symmetrisation has the same alphabet**, at a general family, so
clause (a) of `↪_h` needs no transport. -/
theorem alphabet_eq_of_symmetrizedBase' (D D' : RelGenSet G Λ)
    (hbase : D'.base = {x : G | x ∈ D.base ∨ x⁻¹ ∈ D.base})
    (hfam : D'.fam = D.fam) :
    D'.alphabet.carrier = D.alphabet.carrier := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro y (hy | hy)
    · rw [hbase] at hy
      exact symmetrizedBase_subset_alphabet' D hy
    · rw [hfam] at hy
      exact Set.mem_union_right _ hy
  · rintro y (hy | hy)
    · refine Set.mem_union_left _ ?_
      rw [hbase]
      exact Or.inl hy
    · refine Set.mem_union_right _ ?_
      rw [hfam]
      exact hy

/-- **Every hyperbolically embedded finite family is hyperbolically embedded
with respect to a symmetric relative generating set**, unconditionally.

The general-`Λ` form of `exists_symmetric_base`.  The added letters
`{x | x ∉ X ∧ x⁻¹ ∈ X}` lie in the family --- each in one of its subgroups, not
necessarily the same one --- and form a finite set by `finite_base_asymmetry'`;
the alphabet is unchanged, so hyperbolicity is not transported but reused, and
local finiteness moves one `λ` at a time by
`relBall_finite_of_base_subset'`. -/
theorem exists_symmetric_base' [Finite Λ] (D : RelGenSet G Λ)
    (hemb : D.IsHyperbolicallyEmbedded) :
    ∃ D' : RelGenSet G Λ, D.base ⊆ D'.base ∧ D'.fam = D.fam ∧
      (∀ x ∈ D'.base, x⁻¹ ∈ D'.base) ∧ D'.IsHyperbolicallyEmbedded ∧
        D'.alphabet = D.alphabet := by
  have hsub : D.base ∪ (⋃ lam : Λ, ((D.fam lam : Subgroup G) : Set G))
      ⊆ {x : G | x ∈ D.base ∨ x⁻¹ ∈ D.base} ∪
        (⋃ lam : Λ, ((D.fam lam : Subgroup G) : Set G)) := by
    rintro y (hy | hy)
    · exact Or.inl (Or.inl hy)
    · exact Or.inr hy
  have hgen : IsSymmetricGeneratingSet
      ({x : G | x ∈ D.base ∨ x⁻¹ ∈ D.base} ∪
        (⋃ lam : Λ, ((D.fam lam : Subgroup G) : Set G))) := by
    constructor
    · rintro y (hy | hy)
      · rcases hy with hy | hy
        · refine Or.inl (Or.inr ?_)
          rwa [inv_inv]
        · exact Or.inl (Or.inl hy)
      · obtain ⟨lam, hlam⟩ := Set.mem_iUnion.mp hy
        have hlam' : y ∈ D.fam lam := hlam
        exact Or.inr (Set.mem_iUnion.mpr ⟨lam, inv_mem hlam'⟩)
    · have hmono := Subgroup.closure_mono hsub
      rw [D.symmetricGenerating.closure_eq] at hmono
      exact top_le_iff.mp hmono
  have hN : ∀ x ∈ {x : G | x ∉ D.base ∧ x⁻¹ ∈ D.base}, ∃ mu : Λ, x ∈ D.fam mu := by
    rintro x ⟨hxn, hxi⟩
    have hxinvA : x⁻¹ ∈ D.alphabet.carrier := Set.mem_union_left _ hxi
    have hxA : x ∈ D.base ∪ (⋃ lam : Λ, ((D.fam lam : Subgroup G) : Set G)) := by
      have hstep := D.symmetricGenerating.inv_mem x⁻¹ hxinvA
      rwa [inv_inv] at hstep
    rcases hxA with hb | hf
    · exact absurd hb hxn
    · obtain ⟨lam, hlam⟩ := Set.mem_iUnion.mp hf
      exact ⟨lam, hlam⟩
  have hNfin : {x : G | x ∉ D.base ∧ x⁻¹ ∈ D.base}.Finite := by
    refine ((finite_base_asymmetry' D hemb).image (fun y : G => y⁻¹)).subset ?_
    rintro x ⟨hxn, hxi⟩
    refine ⟨x⁻¹, ⟨hxi, ?_⟩, inv_inv x⟩
    rwa [inv_inv]
  have hbase' : {x : G | x ∈ D.base ∨ x⁻¹ ∈ D.base}
      ⊆ D.base ∪ {x : G | x ∉ D.base ∧ x⁻¹ ∈ D.base} := by
    intro x hx
    by_cases hxb : x ∈ D.base
    · exact Or.inl hxb
    · rcases hx with hx | hx
      · exact absurd hx hxb
      · exact Or.inr ⟨hxb, hx⟩
  have halph : (⟨{x : G | x ∈ D.base ∨ x⁻¹ ∈ D.base}, D.fam, hgen⟩ :
      RelGenSet G Λ).alphabet = D.alphabet :=
    alphabet_eq_of_carrier_eq
      (alphabet_eq_of_symmetrizedBase' D
        ⟨{x : G | x ∈ D.base ∨ x⁻¹ ∈ D.base}, D.fam, hgen⟩ rfl rfl)
  have htransport : ∀ A B : Alphabet G, A = B →
      (∃ δ : ℝ, IsHyperbolicSpace δ (Cayley B)) →
        ∃ δ : ℝ, IsHyperbolicSpace δ (Cayley A) := by
    intro A B hAB hB
    subst hAB
    exact hB
  have hembD' : (⟨{x : G | x ∈ D.base ∨ x⁻¹ ∈ D.base}, D.fam, hgen⟩ :
      RelGenSet G Λ).IsHyperbolicallyEmbedded := by
    constructor
    · exact htransport _ _ halph hemb.hyperbolic
    · intro lam n
      exact relBall_finite_of_base_subset' D
        ⟨{x : G | x ∈ D.base ∨ x⁻¹ ∈ D.base}, D.fam, hgen⟩ lam rfl hN hNfin
        hbase' (fun m => hemb.locallyFinite lam m) n
  refine ⟨⟨{x : G | x ∈ D.base ∨ x⁻¹ ∈ D.base}, D.fam, hgen⟩,
    ?_, rfl, ?_, hembD', halph⟩
  · intro y hy
    exact Or.inl hy
  · intro y hy
    rcases hy with hy | hy
    · refine Or.inr ?_
      rwa [inv_inv]
    · exact Or.inl hy

end OsinComponents
end GGT
end GroupApproximation
