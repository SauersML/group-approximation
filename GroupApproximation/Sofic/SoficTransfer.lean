import GroupApproximation.Sofic.Sofic

/-!
# Transfer of sofic approximations

Two facts used silently in Section `subsec:partitions` of the manuscript:

* restricting a sofic approximation of `G` along an injective homomorphism
  gives a sofic approximation of the source -- this is what makes `σₙ|_Γ` a
  sofic approximation of `Γ`, so that Kun's theorem may be applied to `Γ`;
* soficity passes to subgroups.

Both are proved from the definition, with no extra hypotheses.
-/

namespace GroupApproximation

variable {G H : Type*} [Group G] [Group H]

/-- Soficity passes along injective homomorphisms, in particular to
subgroups. -/
theorem isSofic_of_injective (f : H →* G)
    (hf : Function.Injective f) (h : IsSofic G) : IsSofic H := by
  intro F ε hε
  classical
  obtain ⟨M⟩ := h (F.image f) ε hε
  exact ⟨{
    carrier := M.carrier
    nonempty := M.nonempty
    map := fun x ↦ M.map (f x)
    multiplicative := by
      intro g hg k hk
      simpa using M.multiplicative (f g) (Finset.mem_image.mpr ⟨g, hg, rfl⟩)
        (f k) (Finset.mem_image.mpr ⟨k, hk, rfl⟩)
    separated := by
      intro g hg k hk hne
      exact M.separated (f g) (Finset.mem_image.mpr ⟨g, hg, rfl⟩)
        (f k) (Finset.mem_image.mpr ⟨k, hk, rfl⟩) (fun heq ↦ hne (hf heq)) }⟩

/-- Soficity is invariant under group isomorphism. -/
theorem isSofic_mulEquiv_iff (e : G ≃* H) : IsSofic G ↔ IsSofic H :=
  ⟨fun hG ↦ isSofic_of_injective e.symm.toMonoidHom e.symm.injective hG,
    fun hH ↦ isSofic_of_injective e.toMonoidHom e.injective hH⟩

end GroupApproximation
