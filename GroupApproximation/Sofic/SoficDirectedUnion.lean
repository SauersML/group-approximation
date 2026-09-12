import GroupApproximation.Sofic.Sofic
import Mathlib.Algebra.Group.Subgroup.Basic

/-!
# Soficity is local over subgroups

The local definition of soficity makes directed-union permanence immediate:
if every finite subset of a group is contained in a sofic subgroup, then the
whole group is sofic.  This is the precise form needed for finite-floor lamp
groups and automorphic direct limits.
-/

namespace GroupApproximation

universe u

variable {G : Type u} [Group G]

/-- **Local-subgroup permanence for soficity.**  If every finite subset of
`G` lies in some sofic subgroup, then `G` is sofic. -/
theorem isSofic_of_every_finset_mem_sofic_subgroup
    (hlocal : ∀ F : Finset G, ∃ K : Subgroup G,
      IsSofic K ∧ ∀ g ∈ F, g ∈ K) :
    IsSofic G := by
  classical
  intro F epsilon hepsilon
  obtain ⟨K, hKsofic, hFK⟩ := hlocal F
  let liftToK : G → K := fun g ↦
    if hg : g ∈ K then ⟨g, hg⟩ else 1
  let finiteK : Finset K := F.attach.image fun g ↦
    ⟨g.1, hFK g.1 g.2⟩
  obtain ⟨M⟩ := hKsofic finiteK epsilon hepsilon
  refine ⟨{
    carrier := M.carrier
    nonempty := M.nonempty
    map := fun g ↦ M.map (liftToK g)
    multiplicative := ?_
    separated := ?_ }⟩
  · intro g hg k hk
    have hgK : g ∈ K := hFK g hg
    have hkK : k ∈ K := hFK k hk
    have hgmem : liftToK g ∈ finiteK := by
      apply Finset.mem_image.mpr
      exact ⟨⟨g, hg⟩, Finset.mem_attach _ _, by
        simp [liftToK, hgK]⟩
    have hkmem : liftToK k ∈ finiteK := by
      apply Finset.mem_image.mpr
      exact ⟨⟨k, hk⟩, Finset.mem_attach _ _, by
        simp [liftToK, hkK]⟩
    have hmul : liftToK (g * k) = liftToK g * liftToK k := by
      apply Subtype.ext
      simp [liftToK, hgK, hkK, K.mul_mem hgK hkK]
    rw [hmul]
    exact M.multiplicative _ hgmem _ hkmem
  · intro g hg k hk hgk
    have hgK : g ∈ K := hFK g hg
    have hkK : k ∈ K := hFK k hk
    have hgmem : liftToK g ∈ finiteK := by
      apply Finset.mem_image.mpr
      exact ⟨⟨g, hg⟩, Finset.mem_attach _ _, by
        simp [liftToK, hgK]⟩
    have hkmem : liftToK k ∈ finiteK := by
      apply Finset.mem_image.mpr
      exact ⟨⟨k, hk⟩, Finset.mem_attach _ _, by
        simp [liftToK, hkK]⟩
    apply M.separated _ hgmem _ hkmem
    intro h
    apply hgk
    simpa [liftToK, hgK, hkK] using congrArg Subtype.val h

/-- An increasing union of sofic subgroups is sofic.  This sequence form is
the one used by finite-floor constructions. -/
theorem isSofic_of_increasing_union
    (K : ℕ → Subgroup G)
    (hmono : Monotone K)
    (hK : ∀ n, IsSofic (K n))
    (hcover : ∀ g : G, ∃ n, g ∈ K n) :
    IsSofic G := by
  classical
  apply isSofic_of_every_finset_mem_sofic_subgroup
  intro F
  have hfinite : ∀ A : Finset G, ∃ n, ∀ g ∈ A, g ∈ K n := by
    intro A
    induction A using Finset.induction with
    | empty =>
        exact ⟨0, by simp⟩
    | @insert g A hg ih =>
        obtain ⟨ng, hng⟩ := hcover g
        obtain ⟨nA, hnA⟩ := ih
        refine ⟨max ng nA, ?_⟩
        intro x hx
        rw [Finset.mem_insert] at hx
        rcases hx with rfl | hx
        · exact hmono (Nat.le_max_left _ _) hng
        · exact hmono (Nat.le_max_right _ _) (hnA x hx)
  obtain ⟨n, hn⟩ := hfinite F
  exact ⟨K n, hK n, hn⟩

end GroupApproximation
