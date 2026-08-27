import GroupApproximation.Algebra.FiniteResidual

/-!
# The visible quotient by a finite-residual subgroup

Sections 42, 48 and the factorization half of section 47 of the ascending-HNN
dossier, in their purely group-theoretic form.

Fix a normal subgroup `N` of `G` contained in `finiteResidual G`.  Nothing
below knows anything about matrices: the entire content is that a subgroup of
the finite residual is invisible to every finite target, and that the
correspondence theorem therefore applies to *all* finite-index subgroups rather
than only to those containing a prescribed kernel.

* `finiteResidual_le_ker_of_finite`, `finiteResidual_le_ker_of_residuallyFinite`
  — the two kill lemmas.  A homomorphism to a finite group has finite-index
  kernel; a homomorphism to a residually finite group kills the finite residual
  by functoriality (`map_finiteResidual_le`).  A finite action is a
  homomorphism to a finite permutation group, so it is the first case.
* `existsUnique_factor` — the universal factorization: any homomorphism killing
  `N` factors through `G ⧸ N`, uniquely because the quotient map is onto.
* `comap_map_of_finiteIndex`, `map_comap`, `index_comap`, `index_map_of_finiteIndex`
  — the finite-index subgroup lattice of `G` and that of `G ⧸ N` correspond,
  with indices preserved on the nose.
* `normal_map_of_finiteIndex`, `normal_comap` — the correspondence preserves
  normality in both directions.

The point of isolating this is that all five approximation theories of the
dossier factor through the *same* quotient once their radicals are known to sit
inside the finite residual; the argument that they then share finite quotients,
finite-index subgroup lattices and finite actions is this file, used once.
-/

namespace GroupApproximation

universe u v

namespace VisibleQuotient

variable {G : Type u} [Group G]

/-! ## Finite and residually finite targets cannot see the finite residual -/

/-- A homomorphism into a finite group has finite-index kernel. -/
theorem finiteIndex_ker {F : Type v} [Group F] [Finite F] (f : G →* F) :
    f.ker.FiniteIndex := by
  haveI : Finite (F ⧸ (⊥ : Subgroup F)) :=
    Finite.of_surjective _ (QuotientGroup.mk'_surjective (⊥ : Subgroup F))
  have h := finiteIndex_comap_of_normal f (⊥ : Subgroup F)
  rwa [MonoidHom.comap_bot] at h

/-- Every homomorphism to a finite group kills the finite residual. -/
theorem finiteResidual_le_ker_of_finite {F : Type v} [Group F] [Finite F]
    (f : G →* F) : finiteResidual G ≤ f.ker := by
  haveI := finiteIndex_ker f
  rw [SetLike.le_def]
  intro x hx
  exact mem_finiteResidual_iff.mp hx f.ker inferInstance

/-- Every action on a finite set kills the finite residual: a finite
permutation group is a finite group. -/
theorem finiteResidual_le_ker_of_finiteAction {Ω : Type v} [Finite Ω]
    (f : G →* Equiv.Perm Ω) : finiteResidual G ≤ f.ker :=
  finiteResidual_le_ker_of_finite f

/-- Every homomorphism to a residually finite group kills the finite residual.
This is functoriality of the residual, not a new argument. -/
theorem finiteResidual_le_ker_of_residuallyFinite {R : Type v} [Group R]
    (hR : IsResiduallyFinite R) (f : G →* R) : finiteResidual G ≤ f.ker := by
  rw [SetLike.le_def]
  intro x hx
  rw [MonoidHom.mem_ker]
  have hmap : f x ∈ (finiteResidual G).map f := ⟨x, hx, rfl⟩
  have hbot := map_finiteResidual_le f hmap
  rw [hR, Subgroup.mem_bot] at hbot
  exact hbot

variable {N : Subgroup G} [N.Normal]

omit [N.Normal] in
/-- A subgroup of the finite residual is contained in every finite-index
subgroup. -/
theorem le_of_finiteIndex (hN : N ≤ finiteResidual G) (L : Subgroup G)
    [L.FiniteIndex] : N ≤ L := by
  refine le_trans hN ?_
  rw [SetLike.le_def]
  intro x hx
  exact mem_finiteResidual_iff.mp hx L inferInstance

/-! ## Universal factorization -/

/-- Any homomorphism killing `N` factors through `G ⧸ N`, and the factor is
unique because the quotient map is surjective.  Combined with the kill lemmas
above, this is the statement that finite, finite-action and residually finite
targets see `G` only through `G ⧸ N`. -/
theorem existsUnique_factor {H : Type v} [Group H] (f : G →* H)
    (hf : ∀ x ∈ N, f x = 1) :
    ∃! F : (G ⧸ N) →* H, F.comp (QuotientGroup.mk' N) = f := by
  refine ⟨QuotientGroup.lift N f hf, ?_, ?_⟩
  · ext g
    rfl
  · intro F hF
    ext q
    rw [hF]
    rfl

omit [N.Normal] in
/-- The factorization hypothesis in kernel form. -/
theorem mem_ker_of_le_ker {H : Type v} [Group H] {f : G →* H} (h : N ≤ f.ker) :
    ∀ x ∈ N, f x = 1 := fun _ hx => MonoidHom.mem_ker.mp (h hx)

/-! ## The finite-index subgroup lattice corresponds -/

/-- Pushing a finite-index subgroup to the quotient and pulling back returns
it.  This is where `N ≤ finiteResidual G` is used: without it the
correspondence theorem would only apply to subgroups already containing `N`. -/
theorem comap_map_of_finiteIndex (hN : N ≤ finiteResidual G) (L : Subgroup G)
    [L.FiniteIndex] :
    (L.map (QuotientGroup.mk' N)).comap (QuotientGroup.mk' N) = L := by
  have hNL : N ≤ L := le_of_finiteIndex hN L
  ext x
  simp only [Subgroup.mem_comap, Subgroup.mem_map]
  constructor
  · rintro ⟨l, hl, hlx⟩
    have hmem : l⁻¹ * x ∈ N := by
      rw [← QuotientGroup.ker_mk' N, MonoidHom.mem_ker, map_mul, map_inv, hlx,
        inv_mul_cancel]
    have hprod : l * (l⁻¹ * x) ∈ L := L.mul_mem hl (hNL hmem)
    simpa using hprod
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- Pulling a subgroup of the quotient back and pushing it forward returns it;
this direction needs only surjectivity. -/
theorem map_comap (M : Subgroup (G ⧸ N)) :
    (M.comap (QuotientGroup.mk' N)).map (QuotientGroup.mk' N) = M := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_comap]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro hy
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N y
    exact ⟨x, hy, rfl⟩

/-- The correspondence preserves index in the pullback direction. -/
theorem index_comap (M : Subgroup (G ⧸ N)) :
    (M.comap (QuotientGroup.mk' N)).index = M.index :=
  Subgroup.index_comap_of_surjective M (QuotientGroup.mk'_surjective N)

/-- The correspondence preserves index in the pushforward direction, for
finite-index subgroups. -/
theorem index_map_of_finiteIndex (hN : N ≤ finiteResidual G) (L : Subgroup G)
    [L.FiniteIndex] : (L.map (QuotientGroup.mk' N)).index = L.index := by
  have h := index_comap (N := N) (L.map (QuotientGroup.mk' N))
  rw [comap_map_of_finiteIndex hN L] at h
  exact h.symm

/-- Normality transfers along the pullback. -/
theorem normal_comap (M : Subgroup (G ⧸ N)) [M.Normal] :
    (M.comap (QuotientGroup.mk' N)).Normal :=
  Subgroup.Normal.comap inferInstance _

/-- Normality transfers along the pushforward. -/
theorem normal_map_of_finiteIndex (L : Subgroup G) (hL : L.Normal) :
    (L.map (QuotientGroup.mk' N)).Normal := by
  constructor
  intro y hy z
  obtain ⟨x, hx, rfl⟩ := hy
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N z
  refine ⟨g * x * g⁻¹, hL.conj_mem x hx g, ?_⟩
  simp

/-- The pushforward of a finite-index subgroup has finite index. -/
theorem finiteIndex_map_of_finiteIndex (hN : N ≤ finiteResidual G)
    (L : Subgroup G) [L.FiniteIndex] :
    (L.map (QuotientGroup.mk' N)).FiniteIndex := by
  refine ⟨?_⟩
  rw [index_map_of_finiteIndex hN L]
  exact Subgroup.FiniteIndex.index_ne_zero

/-- The pullback of a finite-index subgroup has finite index. -/
theorem finiteIndex_comap (M : Subgroup (G ⧸ N)) [M.FiniteIndex] :
    (M.comap (QuotientGroup.mk' N)).FiniteIndex := by
  refine ⟨?_⟩
  rw [index_comap M]
  exact Subgroup.FiniteIndex.index_ne_zero

end VisibleQuotient

end GroupApproximation
