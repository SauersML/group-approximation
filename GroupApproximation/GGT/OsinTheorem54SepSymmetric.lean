import GroupApproximation.GGT.OsinTheorem54SepFinite

/-!
# The relative generating set may be taken symmetric

`GGT/OsinTheorem54SeparatingCosets.lean` records an obstruction to
`SepData.sep_comm`, and to the symmetry of Osin's `Y`: reversing a path exchanges
each letter for its inverse, `RelGenSet.base` is not required to be closed under
inversion, and an `X`-letter whose inverse is not an `X`-letter has that inverse
in some `H_λ` --- so the reversed path reads a *component* where the original
read an `X`-edge.

This module removes the obstruction rather than working around it.  The letters
at which it can bite are exactly the `x ∈ X` with `x⁻¹ ∉ X`, and every one of
them lies in `X ∩ H_λ`, which is **finite**:

* `finite_base_inter_fam` --- for a hyperbolically embedded family,
  `X ∩ H_λ` is finite, with no hypothesis at all.  Every element of it is at
  `d̂_λ`-distance at most one from `1` by `mem_relBall_of_mem_base`, and the
  radius-one ball is finite by local finiteness.  This strengthens
  `RelGenSet.not_isHyperbolicallyEmbedded_of_fam_subset_base`, which needs the
  whole of `H_λ` inside `X`.
* `finite_base_asymmetry` --- so `{x ∈ X | x⁻¹ ∉ X}` is finite: the inverse of
  such an `x` lies in the alphabet and not in `X`, so it lies in `H`, and `H` is
  a subgroup.

So `X` may be replaced by `{x | x ∈ X ∨ x⁻¹ ∈ X}` for free, and *without*
Dahmani--Guirardel--Osin's Corollary 4.27:

* `alphabet_eq_of_symmetrizedBase` --- the symmetrisation has the **same
  alphabet**, an element whose inverse is a letter being itself a letter.  So
  clause (a) of `↪_h`, the hyperbolicity of `Γ(G, X ⊔ ℋ)`, is literally the same
  statement for the two relative generating sets and needs no transport.
* `OsinComponents.relBall_finite_of_base_subset` --- clause (b), local
  finiteness, is the only thing that moves, and it survives a finite enlargement
  of the base inside the family.
* `exists_symmetric_base` --- every hyperbolically embedded family is
  hyperbolically embedded with respect to a **symmetric** relative generating
  set containing the original one, unconditionally.

That is the normalisation Osin's §4--§5 works under without saying so, and with
it `SepData.sep_comm` --- refuted at an asymmetric base in
`GGT/OsinTheorem54SepCommRefuted.lean` --- becomes a question about symmetric
bases, where path reversal is available.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w

/-! ## The family meets the base in a finite set -/

section Finite

variable {G : Type u} [Group G] {Λ : Type w}

/-- **`X ∩ H_λ` is finite** for a hyperbolically embedded family.

An element of `H_λ` that is also a letter of `X` is joined to `1` by the
one-letter path `base h`, which traverses no edge of `Γ_{H_λ}`, so it lies in the
`d̂_λ`-ball of radius one; and that ball is finite by local finiteness.

This is the quantitative form of the hygiene invariant
`RelGenSet.not_isHyperbolicallyEmbedded_of_fam_subset_base`: coning off `H_λ` is
meaningful only when `H_λ` is not already part of the base, and what the
definition actually forbids is an *infinite* overlap. -/
theorem finite_base_inter_fam (D : RelGenSet G Λ)
    (hemb : D.IsHyperbolicallyEmbedded) (lam : Λ) :
    (D.base ∩ ((D.fam lam : Subgroup G) : Set G)).Finite := by
  refine (hemb.locallyFinite lam 1).subset ?_
  rintro x ⟨hxb, hxf⟩
  exact mem_relBall_of_mem_base D lam hxf hxb

end Finite

/-! ## The base is symmetric up to a finite set -/

section Symmetrize

variable {G : Type u} [Group G]

/-- **The letters whose inverse is not a letter form a finite set.**

If `x ∈ X` and `x⁻¹ ∉ X` then `x⁻¹` still lies in the alphabet `X ⊔ ℋ`, which is
symmetric, so `x⁻¹ ∈ H`; and `H` is a subgroup, so `x ∈ X ∩ H`, which
`finite_base_inter_fam` makes finite. -/
theorem finite_base_asymmetry (D : RelGenSet G Unit)
    (hemb : D.IsHyperbolicallyEmbedded) :
    {y : G | y ∈ D.base ∧ y⁻¹ ∉ D.base}.Finite := by
  refine (finite_base_inter_fam D hemb ()).subset ?_
  rintro y ⟨hyb, hyn⟩
  refine ⟨hyb, ?_⟩
  have hyA : y ∈ D.alphabet.carrier := Set.mem_union_left _ hyb
  have hinvA : y⁻¹ ∈ D.base ∪ (⋃ lam : Unit, ((D.fam lam : Subgroup G) : Set G)) :=
    D.symmetricGenerating.inv_mem y hyA
  rcases hinvA with hbase | hfam
  · exact absurd hbase hyn
  · obtain ⟨lam, hlam⟩ := Set.mem_iUnion.mp hfam
    cases lam
    have hlam' : y⁻¹ ∈ D.fam () := hlam
    have hinv := inv_mem hlam'
    rwa [inv_inv] at hinv

/-- **Symmetrising the base does not enlarge the alphabet.**  An element whose
inverse is a letter is itself a letter, `X ⊔ ℋ` being symmetric even when `X` is
not. -/
theorem symmetrizedBase_subset_alphabet (D : RelGenSet G Unit) :
    {x : G | x ∈ D.base ∨ x⁻¹ ∈ D.base} ⊆ D.alphabet.carrier := by
  rintro x (hx | hx)
  · exact Set.mem_union_left _ hx
  · have hxinv : x⁻¹ ∈ D.alphabet.carrier := Set.mem_union_left _ hx
    have h := D.symmetricGenerating.inv_mem x⁻¹ hxinv
    rwa [inv_inv] at h

/-- **The symmetrisation has the *same* alphabet**, so `Γ(G, X ⊔ ℋ)` is
unchanged by it.

This is what makes `exists_symmetric_base` cost less than
Dahmani--Guirardel--Osin's Corollary 4.27 in general.  Clause (a) of `↪_h` ---
hyperbolicity of `Γ(G, X ⊔ ℋ)` --- is *literally the same statement* for `D` and
for its symmetrisation, no transport needed; only clause (b), local finiteness of
`d̂_λ`, actually moves, the relative balls growing with the base. -/
theorem alphabet_eq_of_symmetrizedBase (D D' : RelGenSet G Unit)
    (hbase : D'.base = {x : G | x ∈ D.base ∨ x⁻¹ ∈ D.base})
    (hfam : D'.fam = D.fam) :
    D'.alphabet.carrier = D.alphabet.carrier := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro y (hy | hy)
    · rw [hbase] at hy
      exact symmetrizedBase_subset_alphabet D hy
    · rw [hfam] at hy
      exact Set.mem_union_right _ hy
  · rintro y (hy | hy)
    · refine Set.mem_union_left _ ?_
      rw [hbase]
      exact Or.inl hy
    · refine Set.mem_union_right _ ?_
      rw [hfam]
      exact hy

/-- **Two alphabets with the same letters are the same alphabet**, the
generating clause being a proposition. -/
theorem alphabet_eq_of_carrier_eq {A B : Alphabet G} (h : A.carrier = B.carrier) :
    A = B := by
  cases A with
  | mk cA hA =>
      cases B with
      | mk cB hB =>
          have h' : cA = cB := h
          subst h'
          rfl

/-- **Every hyperbolically embedded subgroup is hyperbolically embedded with
respect to a symmetric relative generating set**, unconditionally.

The symmetrisation `{x | x ∈ X ∨ x⁻¹ ∈ X}` contains `X` and has the *same*
alphabet (`alphabet_eq_of_symmetrizedBase`), so clause (a) of `↪_h` --- the
hyperbolicity of `Γ(G, X ⊔ ℋ)` --- is literally the same statement and needs no
transport; and clause (b) is
`OsinComponents.relBall_finite_of_base_subset`, the added letters forming a
finite subset of `H` by `finite_base_asymmetry`.

So no appeal to Dahmani--Guirardel--Osin's Corollary 4.27 is needed here.  This
is the normalisation under which path reversal in `Γ(G, X ⊔ ℋ)` is available,
and so the one under which `SepData.sep_comm` --- refuted at an asymmetric base
in `GGT/OsinTheorem54SepCommRefuted.lean` --- can be asked. -/
theorem exists_symmetric_base (D : RelGenSet G Unit)
    (hemb : D.IsHyperbolicallyEmbedded) :
    ∃ D' : RelGenSet G Unit, D.base ⊆ D'.base ∧ D'.fam = D.fam ∧
      (∀ x ∈ D'.base, x⁻¹ ∈ D'.base) ∧ D'.IsHyperbolicallyEmbedded := by
  -- the symmetrised base
  have hsub : D.base ∪ (⋃ lam : Unit, ((D.fam lam : Subgroup G) : Set G))
      ⊆ {x : G | x ∈ D.base ∨ x⁻¹ ∈ D.base} ∪
        (⋃ lam : Unit, ((D.fam lam : Subgroup G) : Set G)) := by
    rintro y (hy | hy)
    · exact Or.inl (Or.inl hy)
    · exact Or.inr hy
  have hgen : IsSymmetricGeneratingSet
      ({x : G | x ∈ D.base ∨ x⁻¹ ∈ D.base} ∪
        (⋃ lam : Unit, ((D.fam lam : Subgroup G) : Set G))) := by
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
  -- the new letters form a finite subset of the family
  have hNsub : {x : G | x ∉ D.base ∧ x⁻¹ ∈ D.base}
      ⊆ ((D.fam () : Subgroup G) : Set G) := by
    rintro x ⟨hxn, hxi⟩
    have hxinvA : x⁻¹ ∈ D.alphabet.carrier := Set.mem_union_left _ hxi
    have hxA : x ∈ D.base ∪ (⋃ lam : Unit, ((D.fam lam : Subgroup G) : Set G)) := by
      have hstep := D.symmetricGenerating.inv_mem x⁻¹ hxinvA
      rwa [inv_inv] at hstep
    rcases hxA with hb | hf
    · exact absurd hb hxn
    · obtain ⟨lam, hlam⟩ := Set.mem_iUnion.mp hf
      cases lam
      exact hlam
  have hNfin : {x : G | x ∉ D.base ∧ x⁻¹ ∈ D.base}.Finite := by
    refine ((finite_base_asymmetry D hemb).image (fun y : G => y⁻¹)).subset ?_
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
  -- the alphabet is unchanged, so hyperbolicity is the same statement
  have halph : (⟨{x : G | x ∈ D.base ∨ x⁻¹ ∈ D.base}, D.fam, hgen⟩ :
      RelGenSet G Unit).alphabet = D.alphabet :=
    alphabet_eq_of_carrier_eq
      (alphabet_eq_of_symmetrizedBase D
        ⟨{x : G | x ∈ D.base ∨ x⁻¹ ∈ D.base}, D.fam, hgen⟩ rfl rfl)
  have htransport : ∀ A B : Alphabet G, A = B →
      (∃ δ : ℝ, IsHyperbolicSpace δ (Cayley B)) →
        ∃ δ : ℝ, IsHyperbolicSpace δ (Cayley A) := by
    intro A B hAB hB
    subst hAB
    exact hB
  have hembD' : (⟨{x : G | x ∈ D.base ∨ x⁻¹ ∈ D.base}, D.fam, hgen⟩ :
      RelGenSet G Unit).IsHyperbolicallyEmbedded := by
    constructor
    · exact htransport _ _ halph hemb.hyperbolic
    · intro lam n
      cases lam
      exact relBall_finite_of_base_subset D
        ⟨{x : G | x ∈ D.base ∨ x⁻¹ ∈ D.base}, D.fam, hgen⟩ rfl hNsub hNfin
        hbase' (fun m => hemb.locallyFinite () m) n
  refine ⟨⟨{x : G | x ∈ D.base ∨ x⁻¹ ∈ D.base}, D.fam, hgen⟩, ?_, rfl, ?_, hembD'⟩
  · intro y hy
    exact Or.inl hy
  · intro y hy
    rcases hy with hy | hy
    · refine Or.inr ?_
      rwa [inv_inv]
    · exact Or.inl hy

end Symmetrize

end OsinComponents
end GGT
end GroupApproximation
