import GroupApproximation.Sofic.HyperlinearReduction
import GroupApproximation.Sofic.CentralCoverInheritance
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Local lifting through a central quotient

This file isolates the elementary finite-table argument behind the Leavitt
prefix-stabilization construction.  No homology is built into the statement:
one supplies compatible endomorphisms of a surjection and the fact that every
finite subset of its kernel is killed by some iterate.  The quotient then
locally embeds into the covering group.
-/

namespace GroupApproximation

/-- Every finite multiplication table in `G` admits an injective partial
homomorphism into `H`.  Unlike `IsTextbookLEF`, the target is fixed and need
not be finite. -/
def IsLocallyEmbeddableInto (G H : Type*) [Group G] [Group H] : Prop :=
  ∀ s : Finset G, ∃ θ : G → H,
    Set.InjOn θ (s : Set G) ∧
      ∀ x ∈ s, ∀ y ∈ s, x * y ∈ s → θ (x * y) = θ x * θ y

/-- Every group locally embeds into itself via the identity map. -/
theorem isLocallyEmbeddableInto_self (G : Type*) [Group G] :
    IsLocallyEmbeddableInto G G := by
  intro s
  refine ⟨id, ?_, ?_⟩
  · intro x _ y _ hxy
    exact hxy
  · intro x _ y _ _
    rfl

namespace LocalCentralQuotientLifting

variable {U Q : Type*} [Group U] [Group Q]

/-- The iterate of a group endomorphism, retained as a bundled homomorphism. -/
def iterateEnd (F : U →* U) : ℕ → U →* U
  | 0 => MonoidHom.id U
  | m + 1 => F.comp (iterateEnd F m)

@[simp] theorem iterateEnd_zero_apply (F : U →* U) (u : U) :
    iterateEnd F 0 u = u := rfl

@[simp] theorem iterateEnd_succ_apply (F : U →* U) (m : ℕ) (u : U) :
    iterateEnd F (m + 1) u = F (iterateEnd F m u) := rfl

/-- Iteration preserves injectivity. -/
theorem iterateEnd_injective {F : U →* U} (hF : Function.Injective F) (m : ℕ) :
    Function.Injective (iterateEnd F m) := by
  induction m with
  | zero => exact Function.injective_id
  | succ m ih => exact hF.comp ih

/-- Compatible endomorphisms remain compatible after every iterate. -/
theorem iterateEnd_projection
    (p : U →* Q) (F : U →* U) (f : Q →* Q)
    (hcompat : p.comp F = f.comp p) (m : ℕ) (u : U) :
    p (iterateEnd F m u) = iterateEnd f m (p u) := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [iterateEnd_succ_apply, iterateEnd_succ_apply]
      have hpoint : ∀ v : U, p (F v) = f (p v) :=
        DFunLike.congr_fun hcompat
      rw [hpoint, ih]

/-- If compatible iteration kills every prescribed finite part of the
kernel of a surjection, then every finite multiplication table in the
quotient lifts injectively to the covering group.

This is the group-theoretic core of the prefix-stabilization argument.  In
the universal-central-extension application, local nilpotence on `H₂`
supplies `hkill`; neither universality nor centrality is needed after that
input has been extracted. -/
theorem isLocallyEmbeddableInto_of_iterate_kills_finite_kernel
    (p : U →* Q) (F : U →* U) (f : Q →* Q)
    (hp : Function.Surjective p)
    (hf : Function.Injective f)
    (hcompat : p.comp F = f.comp p)
    (hkill : ∀ t : Finset U, (∀ z ∈ t, p z = 1) →
      ∃ m : ℕ, ∀ z ∈ t, iterateEnd F m z = 1) :
    IsLocallyEmbeddableInto Q U := by
  classical
  intro s
  let lift : Q → U := fun x => Classical.choose (hp x)
  have lift_spec (x : Q) : p (lift x) = x := Classical.choose_spec (hp x)
  let defects : Finset U := (s ×ˢ s).image fun xy =>
    lift xy.1 * lift xy.2 * (lift (xy.1 * xy.2))⁻¹
  have defects_mem_ker : ∀ z ∈ defects, p z = 1 := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨xy, _, rfl⟩
    simp [map_mul, lift_spec]
  obtain ⟨m, hm⟩ := hkill defects defects_mem_ker
  let θ : Q → U := fun x => iterateEnd F m (lift x)
  refine ⟨θ, ?_, ?_⟩
  · intro x _ y _ hxy
    apply iterateEnd_injective hf m
    rw [← lift_spec x, ← lift_spec y]
    rw [← iterateEnd_projection p F f hcompat,
      ← iterateEnd_projection p F f hcompat]
    exact congrArg p hxy
  · intro x hx y hy _
    have hdefect :
        lift x * lift y * (lift (x * y))⁻¹ ∈ defects := by
      apply Finset.mem_image.mpr
      exact ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩, rfl⟩
    have hd := hm _ hdefect
    rw [map_mul, map_mul, map_inv] at hd
    exact (mul_inv_eq_one.mp hd).symm

/-- Uniform death of the quotient kernel produces a genuine injective section
over an iterate of the quotient endomorphism.  This is the abstract form of
splitting the universal Steinberg cover over a sufficiently deep corner. -/
theorem exists_injective_iterate_section
    (p : U →* Q) (F : U →* U) (f : Q →* Q)
    (hp : Function.Surjective p)
    (hf : Function.Injective f)
    (hcompat : p.comp F = f.comp p)
    (hkill : ∃ m : ℕ, ∀ z : U, p z = 1 → iterateEnd F m z = 1) :
    ∃ (m : ℕ) (s : Q →* U),
      p.comp s = iterateEnd f m ∧ Function.Injective s := by
  classical
  obtain ⟨m, hm⟩ := hkill
  have hker : p.ker ≤ (iterateEnd F m).ker := by
    intro z hz
    apply MonoidHom.mem_ker.mpr
    exact hm z (MonoidHom.mem_ker.mp hz)
  let qlift : U ⧸ p.ker →* U :=
    QuotientGroup.lift p.ker (iterateEnd F m) hker
  let e : U ⧸ p.ker ≃* Q :=
    QuotientGroup.quotientKerEquivOfSurjective p hp
  let s : Q →* U := qlift.comp e.symm.toMonoidHom
  have hsection : p.comp s = iterateEnd f m := by
    apply MonoidHom.ext
    intro x
    obtain ⟨u, rfl⟩ := hp x
    have hinv : e.symm (p u) = QuotientGroup.mk u := by
      apply e.injective
      rw [e.apply_symm_apply]
      change p u = QuotientGroup.kerLift p (QuotientGroup.mk u)
      exact (QuotientGroup.kerLift_mk p u).symm
    change p (qlift (e.symm (p u))) = iterateEnd f m (p u)
    rw [hinv]
    change p (iterateEnd F m u) = iterateEnd f m (p u)
    exact iterateEnd_projection p F f hcompat m u
  refine ⟨m, s, hsection, ?_⟩
  intro x y hxy
  apply iterateEnd_injective hf m
  have hp_eq := congrArg p hxy
  have hx := DFunLike.congr_fun hsection x
  have hy := DFunLike.congr_fun hsection y
  change p (s x) = iterateEnd f m x at hx
  change p (s y) = iterateEnd f m y at hy
  exact hx.symm.trans (hp_eq.trans hy)

/-- A faithfully projected lifted copy normally generates a perfect central
cover of a nontrivial simple group.  This packages the final group-theoretic
step in the deep-corner argument. -/
theorem normalClosure_range_eq_top_of_injective_projection
    [Group.IsPerfect U] [IsSimpleGroup Q]
    (P : CentralExtension U Q) (s : Q →* U)
    (hs : Function.Injective (P.projection.comp s)) :
    Subgroup.normalClosure (Set.range s) = ⊤ := by
  let N : Subgroup U := Subgroup.normalClosure (Set.range s)
  have hNnormal : N.Normal := Subgroup.normalClosure_normal
  have hmapnormal : (N.map P.projection).Normal :=
    hNnormal.map P.projection P.surjective
  have hmap : N.map P.projection = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        (N.map P.projection) hmapnormal with hbot | htop
    · exfalso
      obtain ⟨q, hq⟩ := exists_ne (1 : Q)
      have hsq : s q ∈ N :=
        Subgroup.subset_normalClosure ⟨q, rfl⟩
      have hpsq : P.projection (s q) ∈ N.map P.projection :=
        ⟨s q, hsq, rfl⟩
      rw [hbot] at hpsq
      have hproj : P.projection (s q) = 1 := Subgroup.mem_bot.mp hpsq
      apply hq
      apply hs
      simpa using hproj
    · exact htop
  have hsup : N ⊔ P.projection.ker = ⊤ := by
    rw [← Subgroup.comap_map_eq (f := P.projection) N, hmap,
      Subgroup.comap_top]
  letI : IsMulCommutative P.projection.ker := ⟨⟨by
    intro a b
    apply Subtype.ext
    exact (Subgroup.mem_center_iff.mp (P.ker_le_center a.property) b).symm⟩⟩
  have hcomm : commutator U ≤ N :=
    hNnormal.commutator_le_of_self_sup_commutative_eq_top hsup inferInstance
  apply top_unique
  intro u _
  exact hcomm (Group.IsPerfect.mem_commutator (G := U) (g := u))

end LocalCentralQuotientLifting

namespace IsLocallyEmbeddableInto

variable {G H : Type*} [Group G] [Group H]

/-- Hyperlinearity transfers backward along local embeddings.  This is the
special local substitute for the unavailable general permanence of
hyperlinearity under quotients. -/
theorem isHyperlinear
    (hlocal : IsLocallyEmbeddableInto G H) (hH : IsHyperlinear H) :
    IsHyperlinear G := by
  classical
  apply (isHyperlinear_iff_productRestricted G).mpr
  intro s ε hε
  obtain ⟨θ, hθinj, hθmul⟩ := hlocal s
  obtain ⟨M⟩ := hH (s.image θ) ε hε
  refine ⟨{
    carrier := M.carrier
    nonempty := M.nonempty
    map := fun g => M.map (θ g)
    isUnitary := fun g => M.isUnitary (θ g)
    multiplicative := ?_
    separated := ?_ }⟩
  · intro g hg h hh hgh
    rw [hθmul g hg h hh hgh]
    exact M.multiplicative (θ g) (Finset.mem_image_of_mem θ hg)
      (θ h) (Finset.mem_image_of_mem θ hh)
  · intro g hg h hh hne
    exact M.separated (θ g) (Finset.mem_image_of_mem θ hg)
      (θ h) (Finset.mem_image_of_mem θ hh)
      (fun heq => hne (hθinj hg hh heq))

/-- Soficity likewise transfers backward along local embeddings. -/
theorem isSofic
    (hlocal : IsLocallyEmbeddableInto G H) (hH : IsSofic H) :
    IsSofic G := by
  classical
  apply (isSofic_iff_productRestricted G).mpr
  intro s ε hε
  obtain ⟨θ, hθinj, hθmul⟩ := hlocal s
  obtain ⟨M⟩ := hH (s.image θ) ε hε
  refine ⟨{
    carrier := M.carrier
    nonempty := M.nonempty
    map := fun g => M.map (θ g)
    multiplicative := ?_
    separated := ?_ }⟩
  · intro g hg h hh hgh
    rw [hθmul g hg h hh hgh]
    exact M.multiplicative (θ g) (Finset.mem_image_of_mem θ hg)
      (θ h) (Finset.mem_image_of_mem θ hh)
  · intro g hg h hh hne
    exact M.separated (θ g) (Finset.mem_image_of_mem θ hg)
      (θ h) (Finset.mem_image_of_mem θ hh)
      (fun heq => hne (hθinj hg hh heq))

end IsLocallyEmbeddableInto
end GroupApproximation
