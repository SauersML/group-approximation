import GroupApproximation.Dynamics.DoubleKernel
import GroupApproximation.Dynamics.FinitarySurjunctivity
import GroupApproximation.Sofic.FreeGroupResiduallyFinite

/-!
# Finitary sites for symmetric doubles

For a pointed set `(X, x₀)` with a group action, the free kernel on the
non-base sites carries the finitary site structure of `Dynamics/FinitarySite`.

* The site group at a finite set `S` is free on the non-base sites of `S`, and
  the projection deletes every letter outside `S`.
* A kernel element is supported on the sites of finitely many letters that
  generate it, together with the basepoint.
* Translation moves a letter and the basepoint together, which gives finite
  support.
* A pointwise stabilizer of `S` fixes the letters inside `S` and moves letters
  outside `S` to letters outside `S`, which gives stabilizer invariance.

For `X = A ⧸ Γ` pointed at the trivial coset, the permanence theorem for
finitary split extensions and `doubleModelEquiv` show that the symmetric
double `A *_Γ A` of a surjunctive group is surjunctive, for every subgroup.
-/

namespace GroupApproximation.Surjunctivity.DoubleKernel

universe u v

variable {X : Type u} (x₀ : X)

/-- The site group at a finite set of sites: free on its non-base sites. -/
abbrev SiteGroup (S : Finset X) : Type u := FreeGroup {s : S // (s : X) ≠ x₀}

/-- The letter of a point in the site group at `S`: its generator when it is a
non-base site of `S`, and `1` otherwise. -/
noncomputable def siteLetter (S : Finset X) (x : X) : SiteGroup x₀ S := by
  classical
  exact if hS : x ∈ S then (if hx : x = x₀ then 1 else FreeGroup.of ⟨⟨x, hS⟩, hx⟩) else 1

@[simp] theorem siteLetter_base (S : Finset X) : siteLetter x₀ S x₀ = 1 := by
  simp [siteLetter]

theorem siteLetter_of_not_mem {S : Finset X} {x : X} (hS : x ∉ S) :
    siteLetter x₀ S x = 1 := by
  simp [siteLetter, hS]

theorem siteLetter_of_mem {S : Finset X} {x : X} (hS : x ∈ S) (hx : x ≠ x₀) :
    siteLetter x₀ S x = FreeGroup.of ⟨⟨x, hS⟩, hx⟩ := by
  simp [siteLetter, hS, hx]

/-- Delete every letter outside `S`. -/
noncomputable def siteProject (S : Finset X) : Kernel x₀ →* SiteGroup x₀ S :=
  FreeGroup.lift fun x => siteLetter x₀ S x.1

@[simp] theorem siteProject_of (S : Finset X) (x : {x : X // x ≠ x₀}) :
    siteProject x₀ S (FreeGroup.of x) = siteLetter x₀ S x.1 := by
  simp only [siteProject, FreeGroup.lift_apply_of]

theorem siteProject_letter (S : Finset X) (x : X) :
    siteProject x₀ S (letter x₀ x) = siteLetter x₀ S x := by
  by_cases hx : x = x₀
  · subst x
    rw [letter_base, map_one, siteLetter_base]
  · rw [show letter x₀ x = FreeGroup.of ⟨x, hx⟩ from letter_of x₀ ⟨x, hx⟩]
    exact siteProject_of x₀ S ⟨x, hx⟩

/-- Include a site group back into the kernel. -/
noncomputable def siteInclude (S : Finset X) : SiteGroup x₀ S →* Kernel x₀ :=
  FreeGroup.map fun s => ⟨(s.1 : X), s.2⟩

theorem siteInclude_of (S : Finset X) (s : {s : S // (s : X) ≠ x₀}) :
    siteInclude x₀ S (FreeGroup.of s) = FreeGroup.of ⟨(s.1 : X), s.2⟩ := by
  simp only [siteInclude, FreeGroup.map.of]

theorem siteProject_siteInclude (S : Finset X) :
    (siteProject x₀ S).comp (siteInclude x₀ S) = MonoidHom.id _ := by
  apply FreeGroup.ext_hom
  intro s
  change siteProject x₀ S (siteInclude x₀ S (FreeGroup.of s)) = FreeGroup.of s
  rw [siteInclude_of, siteProject_of, siteLetter_of_mem x₀ s.1.2 s.2]

theorem siteProject_surjective (S : Finset X) : Function.Surjective (siteProject x₀ S) :=
  fun a => ⟨siteInclude x₀ S a, DFunLike.congr_fun (siteProject_siteInclude x₀ S) a⟩

/-- Include the site group of a smaller set of sites. -/
noncomputable def siteEmbed {U S : Finset X} (hUS : U ⊆ S) :
    SiteGroup x₀ U →* SiteGroup x₀ S :=
  FreeGroup.map fun u => ⟨⟨(u.1 : X), hUS u.1.2⟩, u.2⟩

theorem siteEmbed_of {U S : Finset X} (hUS : U ⊆ S) (u : {s : U // (s : X) ≠ x₀}) :
    siteEmbed x₀ hUS (FreeGroup.of u) = FreeGroup.of ⟨⟨(u.1 : X), hUS u.1.2⟩, u.2⟩ := by
  simp only [siteEmbed, FreeGroup.map.of]

theorem siteInclude_comp_siteEmbed {U S : Finset X} (hUS : U ⊆ S) :
    (siteInclude x₀ S).comp (siteEmbed x₀ hUS) = siteInclude x₀ U := by
  apply FreeGroup.ext_hom
  intro u
  change siteInclude x₀ S (siteEmbed x₀ hUS (FreeGroup.of u)) =
    siteInclude x₀ U (FreeGroup.of u)
  simp only [siteEmbed_of, siteInclude_of]

theorem siteEmbed_injective {U S : Finset X} (hUS : U ⊆ S) :
    Function.Injective (siteEmbed x₀ hUS) := by
  intro a b hab
  have h1 : siteInclude x₀ U a = siteInclude x₀ U b := by
    have ha := DFunLike.congr_fun (siteInclude_comp_siteEmbed x₀ hUS) a
    have hb := DFunLike.congr_fun (siteInclude_comp_siteEmbed x₀ hUS) b
    calc siteInclude x₀ U a = siteInclude x₀ S (siteEmbed x₀ hUS a) := ha.symm
      _ = siteInclude x₀ S (siteEmbed x₀ hUS b) := by rw [hab]
      _ = siteInclude x₀ U b := hb
  have hpa := DFunLike.congr_fun (siteProject_siteInclude x₀ U) a
  have hpb := DFunLike.congr_fun (siteProject_siteInclude x₀ U) b
  calc a = siteProject x₀ U (siteInclude x₀ U a) := hpa.symm
    _ = siteProject x₀ U (siteInclude x₀ U b) := by rw [h1]
    _ = b := hpb

theorem siteEmbed_comp {V U S : Finset X} (hVU : V ⊆ U) (hUS : U ⊆ S) :
    (siteEmbed x₀ hUS).comp (siteEmbed x₀ hVU) =
      siteEmbed x₀ (Finset.Subset.trans hVU hUS) := by
  apply FreeGroup.ext_hom
  intro v
  change siteEmbed x₀ hUS (siteEmbed x₀ hVU (FreeGroup.of v)) =
    siteEmbed x₀ (Finset.Subset.trans hVU hUS) (FreeGroup.of v)
  simp only [siteEmbed_of]

/-- The site group at the empty set of sites is trivial. -/
theorem siteGroup_empty_subsingleton : Subsingleton (SiteGroup x₀ (∅ : Finset X)) := by
  haveI : IsEmpty {s : (∅ : Finset X) // (s : X) ≠ x₀} :=
    ⟨fun s => Finset.notMem_empty (s.1 : X) s.1.2⟩
  infer_instance

/-- Every kernel element lies in the subgroup generated by finitely many letters. -/
theorem exists_finset_mem_closure (n : Kernel x₀) :
    ∃ T : Finset {x : X // x ≠ x₀},
      n ∈ Subgroup.closure (FreeGroup.of '' (T : Set {x : X // x ≠ x₀})) := by
  classical
  have hn : n ∈ Subgroup.closure
      (Set.range (FreeGroup.of : {x : X // x ≠ x₀} → Kernel x₀)) := by
    rw [FreeGroup.closure_range_of]
    exact Subgroup.mem_top n
  induction hn using Subgroup.closure_induction with
  | mem _ hy =>
    obtain ⟨x, rfl⟩ := hy
    exact ⟨{x}, Subgroup.subset_closure ⟨x, by simp, rfl⟩⟩
  | one => exact ⟨∅, one_mem _⟩
  | mul _ _ _ _ hy hz =>
    obtain ⟨T₁, h₁⟩ := hy
    obtain ⟨T₂, h₂⟩ := hz
    refine ⟨T₁ ∪ T₂, mul_mem ?_ ?_⟩
    · exact Subgroup.closure_mono
        (Set.image_mono (Finset.coe_subset.mpr Finset.subset_union_left)) h₁
    · exact Subgroup.closure_mono
        (Set.image_mono (Finset.coe_subset.mpr Finset.subset_union_right)) h₂
  | inv _ _ hy =>
    obtain ⟨T, h⟩ := hy
    exact ⟨T, inv_mem h⟩

/-- The sites of finitely many letters generating a kernel element, together
with the basepoint. -/
noncomputable def kernelSupport (n : Kernel x₀) : Finset X :=
  Finset.cons x₀
    ((Classical.choose (exists_finset_mem_closure x₀ n)).map
      (Function.Embedding.subtype fun x : X => x ≠ x₀))
    (fun h => by
      obtain ⟨t, _, ht⟩ := Finset.mem_map.mp h
      exact t.2 ht)

theorem base_mem_kernelSupport (n : Kernel x₀) : x₀ ∈ kernelSupport x₀ n :=
  Finset.mem_cons_self _ _

theorem mem_closure_kernelSupport (n : Kernel x₀) :
    n ∈ Subgroup.closure
      (FreeGroup.of '' {x : {x : X // x ≠ x₀} | (x : X) ∈ kernelSupport x₀ n}) := by
  refine Subgroup.closure_mono ?_ (Classical.choose_spec (exists_finset_mem_closure x₀ n))
  rintro _ ⟨x, hx, rfl⟩
  have hx' : (x : X) ∈ kernelSupport x₀ n :=
    Finset.mem_cons_of_mem (Finset.mem_map_of_mem (Function.Embedding.subtype _) hx)
  exact ⟨x, hx', rfl⟩

/-- A kernel element generated by letters inside `S` survives projection to `S`. -/
theorem siteInclude_siteProject_of_mem_closure (S : Finset X) {n : Kernel x₀}
    (hn : n ∈ Subgroup.closure (FreeGroup.of '' {x : {x : X // x ≠ x₀} | (x : X) ∈ S})) :
    siteInclude x₀ S (siteProject x₀ S n) = n := by
  have hle : Subgroup.closure (FreeGroup.of '' {x : {x : X // x ≠ x₀} | (x : X) ∈ S}) ≤
      ((siteInclude x₀ S).comp (siteProject x₀ S)).eqLocus (MonoidHom.id _) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨x, hx, rfl⟩
    have hx' : (x : X) ∈ S := hx
    change siteInclude x₀ S (siteProject x₀ S (FreeGroup.of x)) = FreeGroup.of x
    rw [siteProject_of, siteLetter_of_mem x₀ hx' x.2, siteInclude_of]
  exact hle hn

theorem siteProject_detect (E : Finset (Kernel x₀)) (hE : ∀ n ∈ E, n ≠ 1) :
    ∃ S : Finset X, ∀ n ∈ E, siteProject x₀ S n ≠ 1 := by
  classical
  refine ⟨E.biUnion (kernelSupport x₀), fun n hn hproj => hE n hn ?_⟩
  have hsub : {x : {x : X // x ≠ x₀} | (x : X) ∈ kernelSupport x₀ n} ⊆
      {x : {x : X // x ≠ x₀} | (x : X) ∈ E.biUnion (kernelSupport x₀)} :=
    fun x (hx : (x : X) ∈ kernelSupport x₀ n) =>
      (Finset.mem_biUnion.mpr ⟨n, hn, hx⟩ : (x : X) ∈ E.biUnion (kernelSupport x₀))
  have hmem := Subgroup.closure_mono (Set.image_mono hsub) (mem_closure_kernelSupport x₀ n)
  calc n = siteInclude x₀ _ (siteProject x₀ _ n) :=
        (siteInclude_siteProject_of_mem_closure x₀ _ hmem).symm
    _ = 1 := by rw [hproj, map_one]

/-- Enlarging the set of sites does not change the letter of a point that is
not added. -/
theorem siteEmbed_siteLetter {U S : Finset X} (hUS : U ⊆ S) (y : X)
    (hy : y ∈ S → y ∈ U) :
    siteEmbed x₀ hUS (siteLetter x₀ U y) = siteLetter x₀ S y := by
  by_cases hyx : y = x₀
  · subst y
    rw [siteLetter_base, siteLetter_base, map_one]
  · by_cases hyU : y ∈ U
    · rw [siteLetter_of_mem x₀ hyU hyx, siteLetter_of_mem x₀ (hUS hyU) hyx, siteEmbed_of]
    · rw [siteLetter_of_not_mem x₀ hyU,
        siteLetter_of_not_mem x₀ (show y ∉ S from fun hyS => hyU (hy hyS)), map_one]

theorem letter_mem_eqLocus {U S : Finset X} (hUS : U ⊆ S) (y : X) (hy : y ∈ S → y ∈ U) :
    letter x₀ y ∈ (siteProject x₀ S).eqLocus ((siteEmbed x₀ hUS).comp (siteProject x₀ U)) := by
  change siteProject x₀ S (letter x₀ y) = siteEmbed x₀ hUS (siteProject x₀ U (letter x₀ y))
  rw [siteProject_letter, siteProject_letter, siteEmbed_siteLetter x₀ hUS y hy]

variable {G : Type v} [Group G] [MulAction G X]

theorem siteProject_finiteSupport (n : Kernel x₀) (g : G) {U S : Finset X} (hUS : U ⊆ S)
    (h : ∀ x ∈ kernelSupport x₀ n, g • x ∈ S → g • x ∈ U) :
    siteProject x₀ S (action x₀ g n) =
      siteEmbed x₀ hUS (siteProject x₀ U (action x₀ g n)) := by
  let L := (siteProject x₀ S).eqLocus ((siteEmbed x₀ hUS).comp (siteProject x₀ U))
  have hgen : FreeGroup.of '' {x : {x : X // x ≠ x₀} | (x : X) ∈ kernelSupport x₀ n} ⊆
      (L.comap (action x₀ g).toMonoidHom : Set (Kernel x₀)) := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' : (x : X) ∈ kernelSupport x₀ n := hx
    change action x₀ g (FreeGroup.of x) ∈ L
    rw [← letter_of x₀ x, action_letter]
    exact mul_mem (letter_mem_eqLocus x₀ hUS _ (h _ hx'))
      (inv_mem (letter_mem_eqLocus x₀ hUS _ (h x₀ (base_mem_kernelSupport x₀ n))))
  exact (Subgroup.closure_le _).mpr hgen (mem_closure_kernelSupport x₀ n)

theorem siteLetter_smul_of_fixes {S : Finset X} {k : G} (hk : ∀ x ∈ S, k • x = x)
    (y : X) : siteLetter x₀ S (k • y) = siteLetter x₀ S y := by
  by_cases hyS : y ∈ S
  · rw [hk y hyS]
  · have hkyS : k • y ∉ S := by
      intro hkyS
      have hfix : k • y = y := by
        have h2 := congrArg (fun z => k⁻¹ • z) (hk (k • y) hkyS)
        simpa only [inv_smul_smul] using h2
      exact hyS (hfix ▸ hkyS)
    rw [siteLetter_of_not_mem x₀ hkyS, siteLetter_of_not_mem x₀ hyS]

theorem siteProject_stabilizer (S : Finset X) (k : G) (hk : ∀ x ∈ S, k • x = x)
    (n : Kernel x₀) : siteProject x₀ S (action x₀ k n) = siteProject x₀ S n := by
  have hhom : (siteProject x₀ S).comp (action x₀ k).toMonoidHom = siteProject x₀ S := by
    apply FreeGroup.ext_hom
    intro x
    change siteProject x₀ S (action x₀ k (FreeGroup.of x)) = siteProject x₀ S (FreeGroup.of x)
    rw [← letter_of x₀ x, action_letter]
    simp only [map_mul, map_inv, siteProject_letter, siteLetter_smul_of_fixes x₀ hk,
      siteLetter_base, inv_one, mul_one]
  exact DFunLike.congr_fun hhom n

/-- The pointed free kernel carries the finitary site structure. -/
noncomputable def doubleFinitarySite :
    FinitarySite (action x₀ (G := G)) (fun S : Finset X => SiteGroup x₀ S) where
  project := siteProject x₀
  project_surjective := siteProject_surjective x₀
  residuallyFinite := fun _ => isResiduallyFinite_iff_group_residuallyFinite.mpr inferInstance
  empty_subsingleton := siteGroup_empty_subsingleton x₀
  embed := siteEmbed x₀
  embed_injective := siteEmbed_injective x₀
  embed_comp := siteEmbed_comp x₀
  detect := siteProject_detect x₀
  support := kernelSupport x₀
  finiteSupport := siteProject_finiteSupport x₀
  stabilizer_invariance := siteProject_stabilizer x₀

section Double

variable (A : Type u) [Group A] (Γ : Subgroup A)

/-- The free-kernel model of the symmetric double of a surjunctive group is surjunctive. -/
theorem isSurjunctive_model (hA : IsSurjunctive A) : IsSurjunctive (Model A Γ) :=
  (doubleFinitarySite (baseSite A Γ) (G := A)).isSurjunctive hA

end Double

end GroupApproximation.Surjunctivity.DoubleKernel

namespace GroupApproximation.Surjunctivity

universe w

/-- **The symmetric double of a surjunctive group is surjunctive**, over every
subgroup. -/
theorem isSurjunctive_symmetricDouble {G : Type w} [Group G] (Γ : Subgroup G)
    (hG : IsSurjunctive G) : IsSurjunctive (SymmetricDouble G Γ) :=
  (DoubleKernel.isSurjunctive_model G Γ hG).of_mulEquiv (DoubleKernel.doubleModelEquiv G Γ)

/-- A symmetric double is surjunctive exactly when the group is. -/
theorem isSurjunctive_symmetricDouble_iff {G : Type w} [Group G] (Γ : Subgroup G) :
    IsSurjunctive (SymmetricDouble G Γ) ↔ IsSurjunctive G :=
  ⟨fun h => h.of_injective (inDouble G Γ true) (inDouble_injective G Γ true),
    isSurjunctive_symmetricDouble Γ⟩

end GroupApproximation.Surjunctivity
