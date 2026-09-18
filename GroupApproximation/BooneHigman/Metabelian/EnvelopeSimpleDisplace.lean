import GroupApproximation.BooneHigman.Metabelian.EnvelopeSimpleDisplaceClauses
import GroupApproximation.BooneHigman.Metabelian.EnvelopeSimpleDisplaceLocal
import GroupApproximation.Meta.AxiomGuard

/-!
# Displacement in `V_X(H)`

`rnDisplace : RNDisplaceStatement`: every nontrivial element of `⁅V, V⁆`, `V = V_X(H)`,
carries some cone off itself.

Route.
* `determinedSubgroup X`: the permutations `σ` with `σ` and `σ⁻¹` locally determined; a
  subgroup by `LocallyDetermined.comp`.
* `roverNekrashevych_le_determinedSubgroup`: the generators of `V_X(H)` lie in it
  (`locallyDetermined_of_hasDepth`, `locallyDetermined_localize`,
  `locallyDetermined_cantorHom`).
* `exists_disjoint_image_cone`: if `f` is locally determined and `f x ≠ x`, pick `n` with
  `f x n ≠ x n` and `M` such that the first `M` letters of `y` fix the letter `n` of `f y`.
  With `u` the first `M + n + 1` letters of `x`, every `y ∈ cone u` has `f y n = f x n ≠ x n`,
  while every stream of `cone u` has letter `n` equal to `x n`, so `f '' cone u` misses `cone u`.

Neither the commutator nor self-similarity is needed: the displacement holds for all of `V`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

open scoped commutatorElement
open Trees

variable {X : Type*}

variable (X) in
/-- Permutations of the Cantor set that, with their inverses, are locally determined. -/
def determinedSubgroup : Subgroup (Equiv.Perm (Cantor X)) where
  carrier := {σ | LocallyDetermined ⇑σ ∧ LocallyDetermined ⇑σ⁻¹}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨?_, ?_⟩
    · rw [Equiv.Perm.coe_mul]
      exact ha.comp hb
    · rw [mul_inv_rev, Equiv.Perm.coe_mul]
      exact hb'.comp ha'
  one_mem' := by
    refine ⟨?_, ?_⟩
    · rw [Equiv.Perm.coe_one]
      exact locallyDetermined_id
    · rw [inv_one, Equiv.Perm.coe_one]
      exact locallyDetermined_id
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨ha', ?_⟩
    rw [inv_inv]
    exact ha

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.determinedSubgroup

theorem mem_determinedSubgroup {σ : Equiv.Perm (Cantor X)} :
    σ ∈ determinedSubgroup X ↔ LocallyDetermined ⇑σ ∧ LocallyDetermined ⇑σ⁻¹ :=
  Iff.rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.mem_determinedSubgroup

/-- Elements of `V_X(H)` are locally determined, with their inverses. -/
theorem roverNekrashevych_le_determinedSubgroup [Finite X] (H : Subgroup (TreeAut X)) :
    roverNekrashevych X H ≤ determinedSubgroup X := by
  show Subgroup.closure (rnGenerators H) ≤ determinedSubgroup X
  rw [Subgroup.closure_le]
  intro f hf
  rw [rnGenerators, Set.mem_union] at hf
  rcases hf with hf | ⟨w, h, _, rfl⟩
  · have hf' : f ∈ higmanThompsonV X := hf
    obtain ⟨N, hN⟩ := mem_higmanThompsonV.mp hf'
    obtain ⟨M, hM⟩ := mem_higmanThompsonV.mp ((higmanThompsonV X).inv_mem hf')
    exact (mem_determinedSubgroup (σ := f)).mpr
      ⟨locallyDetermined_of_hasDepth hN, locallyDetermined_of_hasDepth hM⟩
  · have e : (localize w (cantorHom h))⁻¹ = localize w (cantorHom h⁻¹) := by
      rw [map_inv cantorHom h, map_inv (localize w) (cantorHom h)]
    refine (mem_determinedSubgroup (σ := localize w (cantorHom h))).mpr
      ⟨locallyDetermined_localize (locallyDetermined_cantorHom h) w, ?_⟩
    rw [e]
    exact locallyDetermined_localize (locallyDetermined_cantorHom h⁻¹) w

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.roverNekrashevych_le_determinedSubgroup

/-- A nontrivial locally determined permutation carries some cone off itself. -/
theorem exists_disjoint_image_cone {f : Equiv.Perm (Cantor X)} (hf : LocallyDetermined ⇑f)
    (hf1 : f ≠ 1) : ∃ u : List X, Disjoint (f '' cone u) (cone u) := by
  obtain ⟨x, hx⟩ : ∃ x, f x ≠ x := Classical.byContradiction fun hcon =>
    hf1 (Equiv.ext fun x => Classical.byContradiction fun h => hcon ⟨x, h⟩)
  obtain ⟨n, hn⟩ := Function.ne_iff.mp hx
  obtain ⟨M, hM⟩ := hf x (n + 1)
  refine ⟨firstWord (M + (n + 1)) x, Set.disjoint_left.mpr ?_⟩
  rintro _ ⟨y, hy, rfl⟩ hfy
  have hxy := streamAgree_of_mem_cone_firstWord hy
  have h1 := hM y (hxy.mono (by omega)) n (by omega)
  have h2 := streamAgree_of_mem_cone_firstWord hfy n (by omega)
  exact hn (h1.trans h2.symm)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.exists_disjoint_image_cone

/-- **Displacement** for Röver–Nekrashevych groups: clause (D) of
`RNDisplaceCompressStatement`. -/
theorem rnDisplace : RNDisplaceStatement := by
  intro X _ _ H _ f hf hf1
  have hfV : f ∈ roverNekrashevych X H := HydeLodha.commutator_le_self _ hf
  exact exists_disjoint_image_cone
    (mem_determinedSubgroup.mp (roverNekrashevych_le_determinedSubgroup H hfV)).1 hf1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rnDisplace

/-- `RNDisplaceCompressStatement` reduces to compression and fragmentation. -/
theorem rnDisplaceCompress_of_compress_fragments (hC : RNCompressStatement)
    (hF : RNFragmentsStatement) : RNDisplaceCompressStatement :=
  rnDisplaceCompress_of_clauses rnDisplace hC hF

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rnDisplaceCompress_of_compress_fragments

end GroupApproximation.BooneHigman.Metabelian.Envelope
