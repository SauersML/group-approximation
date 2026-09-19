import GroupApproximation.Dynamics.ClopenCrossedProductComap
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.Sharpness.Entries
import Mathlib.Topology.Separation.Profinite
import Mathlib.Topology.Instances.ZMod
import GroupApproximation.Meta.AxiomGuard

/-!
# Sharpness over `ℤ`, step 3: a proper invariant closed set destroys simplicity

`simple_kazhdan_sofic_group.tex`, subsection "Sharpness over $\Z$" (Section `sec:main`),
tex l.402–406:

> If a nonempty proper closed set $Y$ is invariant, restriction maps the group onto
> $\EL_3(\LC(Y,\F_2)\rtimes_T\Z)$ with a kernel that contains $e_{12}(e_U)$ for a nonempty clopen
> set $U\subseteq X\setminus Y$ but not $e_{12}(1)$, so the group is not simple.

## Proof route

* `ClopenCrossedProduct.restrict T 𝔽₂ hY : R_X →+* R_Y` is the corpus restriction map, sending
  `C(f) ↦ C(f|_Y)` and `u ↦ u`.
* The map is surjective, since every element of `R_Y` is a Laurent sum `∑ C(f_j) u^j` and every
  `f ∈ LC(Y, 𝔽₂)` extends to `X` (`exists_comap_subtype_eq`). The fibres `{f = 1}` and
  `{f ≠ 1}` are disjoint closed subsets of `X`, so some clopen `C` of the profinite space `X`
  separates them, and then `f = 1_C|_Y`. It follows that `EL₃` of the restriction is surjective.
* As `Y` is closed and proper, some clopen `U ∋ x₀` lies in `X \ Y`. Then `1_U|_Y = 0`, so
  `e₁₂(1_U)` is in the kernel, and `e₁₂(1_U) ≠ 1` because `1_U(x₀) = 1`.
* The element `e₁₂(1)` maps to `e₁₂(1) ≠ 1` in `EL₃(R_Y)`, because `R_Y ≠ 0` for `Y ≠ ∅`.
* The kernel is therefore a normal subgroup that is neither `⊥` nor `⊤`.

The argument is the one in the unwired module `SharpnessExample/Restriction.lean`, redone here in
the lane namespace with rooted imports only.
-/

namespace GroupApproximation.Full.SK07

section E12

variable {R R' : Type*} [Ring R] [Ring R']

/-- `e₁₂(r)` as an element of `EL₃(R)` (tex l.404). -/
noncomputable def e12 (r : R) : elementaryGroup (Fin 3) R :=
  ⟨elementaryUnit 0 1 fin3_zero_ne_one r, elementaryUnit_mem _ _ _ r⟩

theorem elementaryGroupMap_e12 (f : R →+* R') (r : R) :
    elementaryGroupMap f (e12 r) = e12 (f r) := by
  apply Subtype.ext
  rw [elementaryGroupMap_apply]
  exact elementaryMatrixUnitMap_elementaryUnit f 0 1 fin3_zero_ne_one r

theorem e12_eq_one_iff (r : R) : e12 r = 1 ↔ r = 0 := by
  constructor
  · intro h
    have h' : elementaryUnit (0 : Fin 3) 1 fin3_zero_ne_one r =
        elementaryUnit (0 : Fin 3) 1 fin3_zero_ne_one (0 : R) := by
      rw [elementaryUnit_zero]
      exact congrArg Subtype.val h
    exact elementaryUnit_injective _ _ fin3_zero_ne_one h'
  · rintro rfl
    exact Subtype.ext (elementaryUnit_zero _ _ fin3_zero_ne_one)

end E12

section Restriction

variable {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [TotallyDisconnectedSpace X]

/-- **Extension of clopen data.** On a closed subset `Y` of a profinite space, every
`f ∈ LC(Y, 𝔽₂)` is the restriction of some `g ∈ LC(X, 𝔽₂)`. -/
theorem exists_comap_subtype_eq {Y : Set X} (hYc : IsClosed Y) (f : LocallyConstant Y (ZMod 2)) :
    ∃ g : LocallyConstant X (ZMod 2),
      LocallyConstant.comap ⟨Subtype.val, continuous_subtype_val⟩ g = f := by
  have hZ : IsClosed ((Subtype.val : Y → X) '' {y | f y = 1}) :=
    hYc.isClosedMap_subtype_val _ (f.isLocallyConstant.isClopen_fiber 1).isClosed
  have hZ' : IsClosed ((Subtype.val : Y → X) '' {y | f y = 1}ᶜ) :=
    hYc.isClosedMap_subtype_val _ (f.isLocallyConstant.isClopen_fiber 1).compl.isClosed
  have hdisj : (Subtype.val : Y → X) '' {y | f y = 1} ⊆
      ((Subtype.val : Y → X) '' {y | f y = 1}ᶜ)ᶜ := by
    rintro _ ⟨y, hy, rfl⟩ ⟨y', hy', hyy'⟩
    obtain rfl := Subtype.ext hyy'
    exact hy' hy
  obtain ⟨C, hC, hZC, hCZ'⟩ := exists_clopen_of_closed_subset_open hZ hZ'.isOpen_compl hdisj
  refine ⟨LocallyConstant.charFn (ZMod 2) hC, ?_⟩
  ext y
  have key : (y : X) ∈ C ↔ f y = 1 := by
    constructor
    · intro hyC
      by_contra hne
      exact hCZ' hyC ⟨y, hne, rfl⟩
    · intro hy
      exact hZC ⟨y, hy, rfl⟩
  have hval : ∀ a b : ZMod 2, (a = 1 ↔ b = 1) → a = b := by decide
  exact hval _ _ ((LocallyConstant.charFn_eq_one (Y := ZMod 2) (y : X) hC).trans key)

omit [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X] in
/-- A clopen set disjoint from `Y` restricts to `0` on `Y`. -/
theorem comap_subtype_charFn_eq_zero {Y U : Set X} (hU : IsClopen U) (hUY : U ⊆ Yᶜ) :
    LocallyConstant.comap (⟨Subtype.val, continuous_subtype_val⟩ : C(Y, X))
      (LocallyConstant.charFn (ZMod 2) hU) = 0 := by
  ext y
  show LocallyConstant.charFn (ZMod 2) hU (y : X) = 0
  exact (LocallyConstant.charFn_eq_zero (Y := ZMod 2) (y : X) hU).mpr fun h => hUY h y.2

variable (T : X ≃ₜ X)

/-- **Restriction is onto** (tex l.403, "restriction maps the group onto"). For a closed
invariant set `Y`, the restriction `LC(X, 𝔽₂) ⋊_T ℤ → LC(Y, 𝔽₂) ⋊_T ℤ` is surjective. -/
theorem restrict_surjective {Y : Set X} (hYc : IsClosed Y) (hY : T '' Y = Y) :
    Function.Surjective (ClopenCrossedProduct.restrict T (ZMod 2) hY) := by
  intro r
  obtain ⟨S, f, rfl⟩ := ClopenCrossedProduct.exists_sum_coeff_mul_unit_zpow
    (ClopenCrossedProduct.restrictHomeo T hY) (ZMod 2) r
  choose g hg using fun j => exists_comap_subtype_eq hYc (f j)
  refine ⟨∑ j ∈ S, ClopenCrossedProduct.coeff T (ZMod 2) (g j) *
    ((ClopenCrossedProduct.unit T (ZMod 2) ^ j : (ClopenCrossedProduct T (ZMod 2))ˣ) :
      ClopenCrossedProduct T (ZMod 2)), ?_⟩
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hu : ClopenCrossedProduct.restrict T (ZMod 2) hY
      ((ClopenCrossedProduct.unit T (ZMod 2) ^ j : (ClopenCrossedProduct T (ZMod 2))ˣ) :
        ClopenCrossedProduct T (ZMod 2)) =
      ((ClopenCrossedProduct.unit (ClopenCrossedProduct.restrictHomeo T hY) (ZMod 2) ^ j :
          (ClopenCrossedProduct (ClopenCrossedProduct.restrictHomeo T hY) (ZMod 2))ˣ) :
        ClopenCrossedProduct (ClopenCrossedProduct.restrictHomeo T hY) (ZMod 2)) :=
    ClopenCrossedProduct.comap_unit_zpow (T := ClopenCrossedProduct.restrictHomeo T hY) (S := T)
      (ZMod 2) ⟨Subtype.val, continuous_subtype_val⟩ (fun _ => rfl) j
  rw [map_mul, ClopenCrossedProduct.restrict_coeff, hg j, hu]

omit [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X] in
/-- `e₁₂(1_U)` lies in the kernel of the restriction when `U ⊆ X \ Y`. -/
theorem e12_charFn_mem_ker {Y U : Set X} (hY : T '' Y = Y) (hU : IsClopen U) (hUY : U ⊆ Yᶜ) :
    e12 (ClopenCrossedProduct.coeff T (ZMod 2) (LocallyConstant.charFn (ZMod 2) hU)) ∈
      (elementaryGroupMap (ι := Fin 3) (ClopenCrossedProduct.restrict T (ZMod 2) hY)).ker := by
  rw [MonoidHom.mem_ker, elementaryGroupMap_e12, ClopenCrossedProduct.restrict_coeff,
    comap_subtype_charFn_eq_zero hU hUY, map_zero, e12_eq_one_iff]

omit [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X] in
/-- `e₁₂(1_U) ≠ 1` for a nonempty clopen `U`. -/
theorem e12_charFn_ne_one {U : Set X} (hU : IsClopen U) (hne : U.Nonempty) :
    e12 (ClopenCrossedProduct.coeff T (ZMod 2) (LocallyConstant.charFn (ZMod 2) hU)) ≠ 1 := by
  intro h
  obtain ⟨x0, hx0⟩ := hne
  rw [e12_eq_one_iff] at h
  have h0 : LocallyConstant.charFn (ZMod 2) hU = 0 :=
    ClopenCrossedProduct.coeff_injective T (ZMod 2)
      (h.trans (map_zero (ClopenCrossedProduct.coeff T (ZMod 2))).symm)
  have h1 : LocallyConstant.charFn (ZMod 2) hU x0 = 0 := by
    rw [h0, LocallyConstant.zero_apply]
  exact one_ne_zero
    (((LocallyConstant.charFn_eq_one (Y := ZMod 2) x0 hU).mpr hx0).symm.trans h1)

omit [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X] in
/-- `e₁₂(1)` is not in the kernel of the restriction to a nonempty invariant set. -/
theorem e12_one_not_mem_ker {Y : Set X} (hY : T '' Y = Y) (hne : Y.Nonempty) :
    e12 (1 : ClopenCrossedProduct T (ZMod 2)) ∉
      (elementaryGroupMap (ι := Fin 3) (ClopenCrossedProduct.restrict T (ZMod 2) hY)).ker := by
  intro h
  obtain ⟨y0, hy0⟩ := hne
  rw [MonoidHom.mem_ker, elementaryGroupMap_e12,
    map_one (ClopenCrossedProduct.restrict T (ZMod 2) hY), e12_eq_one_iff] at h
  have h0 : (1 : LocallyConstant Y (ZMod 2)) = 0 :=
    ClopenCrossedProduct.coeff_injective (ClopenCrossedProduct.restrictHomeo T hY) (ZMod 2)
      ((map_one
          (ClopenCrossedProduct.coeff (ClopenCrossedProduct.restrictHomeo T hY) (ZMod 2))).trans
        (h.trans
          (map_zero (ClopenCrossedProduct.coeff (ClopenCrossedProduct.restrictHomeo T hY)
            (ZMod 2))).symm))
  have h1 : (1 : LocallyConstant Y (ZMod 2)) ⟨y0, hy0⟩ = 0 := by
    rw [h0, LocallyConstant.zero_apply]
  rw [LocallyConstant.one_apply] at h1
  exact one_ne_zero h1

/-- **Sharpness over `ℤ`, sentence at tex l.402–406.** Let `X` be a profinite space with a
homeomorphism `T`, and let `Y` be a nonempty proper closed invariant set. Restriction maps
`EL₃(LC(X, 𝔽₂) ⋊_T ℤ)` onto `EL₃(LC(Y, 𝔽₂) ⋊_T ℤ)`. There is a nonempty clopen `U ⊆ X \ Y`,
and for every nonempty clopen `U ⊆ X \ Y` the kernel contains `e₁₂(e_U) ≠ 1`. The kernel does not
contain `e₁₂(1)`, so the group is not simple. -/
theorem restrictionNotSimple_sentence {Y : Set X} (hYc : IsClosed Y)
    (hne : Y.Nonempty) (hproper : Y ≠ Set.univ) (hY : T '' Y = Y) :
    Function.Surjective
        (elementaryGroupMap (ι := Fin 3) (ClopenCrossedProduct.restrict T (ZMod 2) hY)) ∧
      (∃ U : Set X, IsClopen U ∧ U.Nonempty ∧ U ⊆ Yᶜ) ∧
      (∀ (U : Set X) (hU : IsClopen U), U.Nonempty → U ⊆ Yᶜ →
        e12 (ClopenCrossedProduct.coeff T (ZMod 2) (LocallyConstant.charFn (ZMod 2) hU)) ∈
          (elementaryGroupMap (ι := Fin 3) (ClopenCrossedProduct.restrict T (ZMod 2) hY)).ker ∧
        e12 (ClopenCrossedProduct.coeff T (ZMod 2) (LocallyConstant.charFn (ZMod 2) hU)) ≠ 1) ∧
      e12 (1 : ClopenCrossedProduct T (ZMod 2)) ∉
        (elementaryGroupMap (ι := Fin 3) (ClopenCrossedProduct.restrict T (ZMod 2) hY)).ker ∧
      ¬ IsSimpleGroup (elementaryGroup (Fin 3) (ClopenCrossedProduct T (ZMod 2))) := by
  obtain ⟨x0, hx0⟩ := (Set.ne_univ_iff_exists_notMem Y).mp hproper
  obtain ⟨U, hU, hx0U, hUY⟩ := compact_exists_isClopen_in_isOpen hYc.isOpen_compl hx0
  have hsurj : Function.Surjective
      (elementaryGroupMap (ι := Fin 3) (ClopenCrossedProduct.restrict T (ZMod 2) hY)) :=
    elementaryGroupMap_surjective_of_surjective _ (restrict_surjective T hYc hY)
  have hker : ∀ (U : Set X) (hU : IsClopen U), U.Nonempty → U ⊆ Yᶜ →
      e12 (ClopenCrossedProduct.coeff T (ZMod 2) (LocallyConstant.charFn (ZMod 2) hU)) ∈
        (elementaryGroupMap (ι := Fin 3) (ClopenCrossedProduct.restrict T (ZMod 2) hY)).ker ∧
      e12 (ClopenCrossedProduct.coeff T (ZMod 2) (LocallyConstant.charFn (ZMod 2) hU)) ≠ 1 :=
    fun _ hU hUne hUY => ⟨e12_charFn_mem_ker T hY hU hUY, e12_charFn_ne_one T hU hUne⟩
  have hone := e12_one_not_mem_ker T hY hne
  refine ⟨hsurj, ⟨U, hU, ⟨x0, hx0U⟩, hUY⟩, hker, hone, ?_⟩
  intro hsimple
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal _
      (elementaryGroupMap (ι := Fin 3) (ClopenCrossedProduct.restrict T (ZMod 2) hY)).normal_ker
    with hbot | htop
  · have hmem := (hker U hU ⟨x0, hx0U⟩ hUY).1
    rw [hbot, Subgroup.mem_bot] at hmem
    exact (hker U hU ⟨x0, hx0U⟩ hUY).2 hmem
  · exact hone (by rw [htop]; exact Subgroup.mem_top _)

#audit_axioms restrictionNotSimple_sentence

/-- A system with a nonempty proper closed invariant set has a non-simple `EL₃`
(tex l.402–406). -/
theorem not_isSimpleGroup_of_invariant {Y : Set X} (hYc : IsClosed Y) (hne : Y.Nonempty)
    (hproper : Y ≠ Set.univ) (hY : T '' Y = Y) :
    ¬ IsSimpleGroup (elementaryGroup (Fin 3) (ClopenCrossedProduct T (ZMod 2))) :=
  (restrictionNotSimple_sentence T hYc hne hproper hY).2.2.2.2

#audit_axioms not_isSimpleGroup_of_invariant

end Restriction

end GroupApproximation.Full.SK07
