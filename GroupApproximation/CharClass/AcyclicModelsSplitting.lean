import GroupApproximation.CharClass.AcyclicModelsTensor
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Projection

/-!
# Over a field, positive-degree acyclicity is a contraction

`AcyclicModelsTensor.lean` reduces the acyclicity of a tensor product to a
homotopy from the identity of each factor to a chain map vanishing in positive
degrees.  Nothing in the repository produced such a homotopy: what is available
for the models is the *vanishing of their homology*, which says only that cycles
are boundaries and gives no splittings.

Over a field the gap closes, and this file closes it.  A complex of vector
spaces whose positive-degree cycles are boundaries admits an explicit
contraction, obtained by choosing, in each degree `j`, a complement `U j` of the
boundaries `im d_{j+1}` inside `K_j`.  Three facts make one choice enough:

* `d_{j+1}` restricted to `U (j+1)` is injective, because its kernel lands in
  `im d_{j+2}`, which meets `U (j+1)` trivially — this is the only place
  acyclicity is used;
* that restriction is onto `im d_{j+1}`, because the `im d_{j+2}` part of any
  preimage is killed by `d_{j+1}`;
* so `s_j :=` (left inverse of the restriction) ∘ (projection onto `im d_{j+1}`
  along `U j`) satisfies `d s + s d = 1` in every positive degree.

In degree `0` the same operator gives `1 - d_1 s_0 =` the projection onto
`U 0`, which is a chain map because `d_1 s_0 d_1 = d_1`, and which vanishes in
positive degrees by construction.  That is exactly the input
`AcyclicModelsTensor.tensorPositiveContraction` wants, so `tensorSplitContraction`
below is the statement "over a field, a tensor product of positive-degree
acyclic complexes is positive-degree acyclic" — the form in which the acyclicity
hypothesis of the acyclic-models theorem is discharged for a tensor square.

The coefficient field in the application is `ZMod 2`, and the complexes are the
singular chains of a standard simplex, whose positive homology vanishes.
-/

universe u v w

namespace GroupApproximation.CharClass

open CategoryTheory CategoryTheory.Limits

variable {F : Type} [Field F] (K : ChainComplex (ModuleCat.{0} F) ℕ)

/-! ## 1. A complement of the boundaries in each degree -/

/-- A chosen complement of the boundaries `im d_{j+1}` inside `K_j`. -/
noncomputable def bdryCompl (j : ℕ) : Submodule F (K.X j) :=
  (LinearMap.range (K.d (j + 1) j).hom).exists_isCompl.choose

lemma bdryCompl_isCompl (j : ℕ) :
    IsCompl (LinearMap.range (K.d (j + 1) j).hom) (bdryCompl K j) :=
  (LinearMap.range (K.d (j + 1) j).hom).exists_isCompl.choose_spec

/-- The projection onto the boundaries, along the chosen complement. -/
noncomputable def bdryProj (j : ℕ) : K.X j →ₗ[F] K.X j :=
  (LinearMap.range (K.d (j + 1) j).hom).projection (bdryCompl K j) (bdryCompl_isCompl K j)

/-- The projection onto the chosen complement, along the boundaries. -/
noncomputable def complProj (j : ℕ) : K.X j →ₗ[F] K.X j :=
  (bdryCompl K j).projection (LinearMap.range (K.d (j + 1) j).hom)
    (bdryCompl_isCompl K j).symm

lemma bdryProj_add_complProj (j : ℕ) (x : K.X j) :
    bdryProj K j x + complProj K j x = x :=
  Submodule.projection_add_projection_eq_self (bdryCompl_isCompl K j) x

lemma bdryProj_mem (j : ℕ) (x : K.X j) :
    bdryProj K j x ∈ LinearMap.range (K.d (j + 1) j).hom :=
  Submodule.projection_apply_mem _ _

lemma complProj_mem (j : ℕ) (x : K.X j) : complProj K j x ∈ bdryCompl K j :=
  Submodule.projection_apply_mem _ _

lemma bdryProj_of_mem (j : ℕ) {y : K.X j}
    (hy : y ∈ LinearMap.range (K.d (j + 1) j).hom) : bdryProj K j y = y :=
  Submodule.projection_apply_of_mem_left _ hy

lemma complProj_of_mem_range (j : ℕ) {y : K.X j}
    (hy : y ∈ LinearMap.range (K.d (j + 1) j).hom) : complProj K j y = 0 :=
  (Submodule.projection_apply_eq_zero_iff _).2 hy

/-- The boundaries are cycles: `d` kills the image of the projection. -/
lemma d_bdryProj (j : ℕ) (x : K.X (j + 1)) :
    (K.d (j + 1) j).hom (bdryProj K (j + 1) x) = 0 := by
  obtain ⟨z, hz⟩ := bdryProj_mem K (j + 1) x
  rw [← hz, ← LinearMap.comp_apply, ← ModuleCat.hom_comp, HomologicalComplex.d_comp_d,
    ModuleCat.hom_zero, LinearMap.zero_apply]

/-! ## 2. The differential restricted to the complement -/

/-- The differential restricted to the chosen complement in the source. -/
noncomputable def dOnCompl (j : ℕ) : bdryCompl K (j + 1) →ₗ[F] K.X j :=
  (K.d (j + 1) j).hom.comp (bdryCompl K (j + 1)).subtype

/-- **Injectivity**, the only use of acyclicity: a cycle in the complement lies
in the boundaries, which meet the complement trivially. -/
lemma dOnCompl_ker (hK : ∀ k : ℕ, LinearMap.ker (K.d (k + 1) k).hom
      ≤ LinearMap.range (K.d (k + 2) (k + 1)).hom) (j : ℕ) :
    LinearMap.ker (dOnCompl K j) = ⊥ := by
  rw [eq_bot_iff]
  intro c hc
  rw [Submodule.mem_bot]
  rw [← Submodule.coe_eq_zero]
  have hc0 : (K.d (j + 1) j).hom (c : K.X (j + 1)) = 0 := hc
  have h1 : (c : K.X (j + 1)) ∈ LinearMap.range (K.d (j + 2) (j + 1)).hom := hK j hc0
  have h2 : (c : K.X (j + 1)) ∈ bdryCompl K (j + 1) := c.2
  have hbot := (bdryCompl_isCompl K (j + 1)).inf_eq_bot
  have hmem : (c : K.X (j + 1)) ∈
      LinearMap.range (K.d (j + 2) (j + 1)).hom ⊓ bdryCompl K (j + 1) := ⟨h1, h2⟩
  rw [hbot, Submodule.mem_bot] at hmem
  exact hmem

/-- **Surjectivity onto the boundaries**: the boundary part of any preimage is
killed by `d`, so the complement part already hits the target. -/
lemma exists_compl_preimage (j : ℕ) {y : K.X j}
    (hy : y ∈ LinearMap.range (K.d (j + 1) j).hom) :
    ∃ c : bdryCompl K (j + 1), (K.d (j + 1) j).hom (c : K.X (j + 1)) = y := by
  obtain ⟨w, rfl⟩ := hy
  refine ⟨⟨complProj K (j + 1) w, complProj_mem K (j + 1) w⟩, ?_⟩
  have hsum := bdryProj_add_complProj K (j + 1) w
  calc (K.d (j + 1) j).hom (complProj K (j + 1) w)
      = (K.d (j + 1) j).hom (bdryProj K (j + 1) w)
          + (K.d (j + 1) j).hom (complProj K (j + 1) w) := by
        rw [d_bdryProj K j w, zero_add]
    _ = (K.d (j + 1) j).hom (bdryProj K (j + 1) w + complProj K (j + 1) w) := by
        rw [map_add]
    _ = (K.d (j + 1) j).hom w := by rw [hsum]

/-- A left inverse of the restricted differential. -/
noncomputable def dSection (j : ℕ) : K.X j →ₗ[F] bdryCompl K (j + 1) :=
  (dOnCompl K j).leftInverse

lemma dSection_d (hK : ∀ k : ℕ, LinearMap.ker (K.d (k + 1) k).hom
      ≤ LinearMap.range (K.d (k + 2) (k + 1)).hom) (j : ℕ) (c : bdryCompl K (j + 1)) :
    dSection K j ((K.d (j + 1) j).hom (c : K.X (j + 1))) = c :=
  LinearMap.leftInverse_apply_of_inj (dOnCompl_ker K hK j) c

/-! ## 3. The contracting operator -/

/-- The contracting operator: project onto the boundaries, then invert the
differential on the complement. -/
noncomputable def splitHom (j : ℕ) : K.X j →ₗ[F] K.X (j + 1) :=
  (bdryCompl K (j + 1)).subtype.comp ((dSection K j).comp (bdryProj K j))

lemma splitHom_apply (j : ℕ) (x : K.X j) :
    splitHom K j x = (dSection K j (bdryProj K j x) : K.X (j + 1)) := rfl

/-- `d ∘ s` is the projection onto the boundaries. -/
lemma d_splitHom (hK : ∀ k : ℕ, LinearMap.ker (K.d (k + 1) k).hom
      ≤ LinearMap.range (K.d (k + 2) (k + 1)).hom) (j : ℕ) (x : K.X j) :
    (K.d (j + 1) j).hom (splitHom K j x) = bdryProj K j x := by
  obtain ⟨c, hc⟩ := exists_compl_preimage K j (bdryProj_mem K j x)
  rw [splitHom_apply, ← hc, dSection_d K hK j c]

/-- `s ∘ d` is the identity on the chosen complement. -/
lemma splitHom_d (hK : ∀ k : ℕ, LinearMap.ker (K.d (k + 1) k).hom
      ≤ LinearMap.range (K.d (k + 2) (k + 1)).hom) (j : ℕ) (c : bdryCompl K (j + 1)) :
    splitHom K j ((K.d (j + 1) j).hom (c : K.X (j + 1))) = (c : K.X (j + 1)) := by
  rw [splitHom_apply, bdryProj_of_mem K j ⟨(c : K.X (j + 1)), rfl⟩, dSection_d K hK j c]

/-- **The contraction identity in positive degrees.** -/
lemma splitHom_comm (hK : ∀ k : ℕ, LinearMap.ker (K.d (k + 1) k).hom
      ≤ LinearMap.range (K.d (k + 2) (k + 1)).hom) (k : ℕ) (x : K.X (k + 1)) :
    (K.d (k + 2) (k + 1)).hom (splitHom K (k + 1) x)
      + splitHom K k ((K.d (k + 1) k).hom x) = x := by
  have hsum := bdryProj_add_complProj K (k + 1) x
  have h1 : (K.d (k + 2) (k + 1)).hom (splitHom K (k + 1) x) = bdryProj K (k + 1) x :=
    d_splitHom K hK (k + 1) x
  have hdx : (K.d (k + 1) k).hom x = (K.d (k + 1) k).hom (complProj K (k + 1) x) := by
    conv_lhs => rw [← hsum]
    rw [map_add, d_bdryProj K k x, zero_add]
  have h2 : splitHom K k ((K.d (k + 1) k).hom x) = complProj K (k + 1) x := by
    rw [hdx]
    exact splitHom_d K hK k ⟨complProj K (k + 1) x, complProj_mem K (k + 1) x⟩
  rw [h1, h2, hsum]

/-! ## 4. The comparison chain map and the homotopy -/

/-- The degreewise components of the comparison map: the projection onto the
chosen complement in degree `0`, and zero above. -/
noncomputable def splitAlphaF : ∀ j : ℕ, K.X j ⟶ K.X j
  | 0 => ModuleCat.ofHom (complProj K 0)
  | _ + 1 => 0

lemma splitAlphaF_succ (k : ℕ) : splitAlphaF K (k + 1) = 0 := rfl

/-- The comparison chain map: concentrated in degree `0`, where it is the
projection onto the chosen complement of the boundaries. -/
noncomputable def splitAlpha : K ⟶ K where
  f := splitAlphaF K
  comm' := by
    rintro i j (rfl : j + 1 = i)
    rcases j with _ | m
    · rw [splitAlphaF_succ, zero_comp]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
        LinearMap.zero_apply]
      show 0 = (splitAlphaF K 0).hom ((K.d 1 0).hom x)
      rw [splitAlphaF, ModuleCat.hom_ofHom, complProj_of_mem_range K 0 ⟨x, rfl⟩]
    · rw [splitAlphaF_succ, splitAlphaF_succ, zero_comp, comp_zero]

@[simp] lemma splitAlpha_f_succ (k : ℕ) : (splitAlpha K).f (k + 1) = 0 := rfl

@[simp] lemma splitAlpha_f_zero :
    (splitAlpha K).f 0 = ModuleCat.ofHom (complProj K 0) := rfl

/-- **The homotopy.**  Over a field, a complex whose positive-degree cycles are
boundaries has its identity homotopic to a chain map concentrated in degree
`0`. -/
noncomputable def splitHomotopy (hK : ∀ k : ℕ, LinearMap.ker (K.d (k + 1) k).hom
      ≤ LinearMap.range (K.d (k + 2) (k + 1)).hom) :
    Homotopy (𝟙 K) (splitAlpha K) := by
  refine Homotopy.equivSubZero.symm
    (homotopyOfFamily (𝟙 K - splitAlpha K)
      (fun k => ModuleCat.ofHom (splitHom K k)) ?_ ?_)
  · rw [HomologicalComplex.sub_f_apply]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    simp only [ModuleCat.hom_sub, LinearMap.sub_apply, HomologicalComplex.id_f,
      ModuleCat.hom_id, LinearMap.id_apply, splitAlpha_f_zero, ModuleCat.hom_comp,
      LinearMap.comp_apply, ModuleCat.hom_ofHom]
    rw [d_splitHom K hK 0 x, sub_eq_iff_eq_add]
    exact (bdryProj_add_complProj K 0 x).symm
  · intro k
    rw [HomologicalComplex.sub_f_apply]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    simp only [splitAlpha_f_succ, sub_zero, HomologicalComplex.id_f, ModuleCat.hom_id,
      LinearMap.id_apply, ModuleCat.hom_add, LinearMap.add_apply, ModuleCat.hom_comp,
      LinearMap.comp_apply, ModuleCat.hom_ofHom]
    exact (splitHom_comm K hK k x).symm.trans (add_comm _ _)

/-! ## 5. Consequences -/

/-- Over a field, positive-degree acyclicity of two complexes gives a contraction
of their tensor product above degree zero. -/
noncomputable def tensorSplitContraction (L : ChainComplex (ModuleCat.{0} F) ℕ)
    (hK : ∀ k : ℕ, LinearMap.ker (K.d (k + 1) k).hom
      ≤ LinearMap.range (K.d (k + 2) (k + 1)).hom)
    (hL : ∀ k : ℕ, LinearMap.ker (L.d (k + 1) k).hom
      ≤ LinearMap.range (L.d (k + 2) (k + 1)).hom) :
    PositiveContraction (tensorCx K L) :=
  tensorPositiveContraction (splitHomotopy K hK) (splitHomotopy L hL)
    (splitAlpha_f_succ K) (splitAlpha_f_succ L)

/-- Over a field, a positive-degree cycle of a tensor product of two
positive-degree acyclic complexes is a boundary. -/
theorem tensorSplit_exists_preimage (L : ChainComplex (ModuleCat.{0} F) ℕ)
    (hK : ∀ k : ℕ, LinearMap.ker (K.d (k + 1) k).hom
      ≤ LinearMap.range (K.d (k + 2) (k + 1)).hom)
    (hL : ∀ k : ℕ, LinearMap.ker (L.d (k + 1) k).hom
      ≤ LinearMap.range (L.d (k + 2) (k + 1)).hom)
    (k : ℕ) (y : (tensorCx K L).X (k + 1))
    (hy : ((tensorCx K L).d (k + 1) k).hom y = 0) :
    ∃ z : (tensorCx K L).X (k + 2), ((tensorCx K L).d (k + 2) (k + 1)).hom z = y :=
  (tensorSplitContraction K L hK hL).exists_preimage k y hy

/-- The acyclicity hypothesis of the acyclic-models theorem, in the form in which
a vanishing-homology computation supplies it. -/
lemma acyclicOnModels_of_ker_le_range {C : Type u} [Category.{v} C] {ι : Type w}
    (M : ι → C) (G : C ⥤ ChainComplex (ModuleCat.{0} F) ℕ)
    (h : ∀ (i : ι) (k : ℕ), LinearMap.ker ((G.obj (M i)).d (k + 1) k).hom
      ≤ LinearMap.range ((G.obj (M i)).d (k + 2) (k + 1)).hom) :
    AcyclicOnModels M F G where
  exists_preimage i k _ hy := h i k hy

end GroupApproximation.CharClass
