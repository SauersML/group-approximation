import GroupApproximation.GGT.ElementaryClosure

/-!
# Hull's (W4) is free at the cyclic subgroups

`HullSC.ExistsHypEmbeddedConeOff₂` -- Hull's Corollary 5.7 with Lemma 5.8 for a
pair -- was strengthened with Hull's condition (W4), that the two hyperbolically
embedded subgroups meet trivially.  Its docstring records the clause as *"part
of what §5 delivers --- Corollary 5.7 gives `E(hᵢ) = ⟨hᵢ⟩` and independence
separates them --- and it is recorded in the citation rather than derived here"*.

**The second half of that sentence is a theorem**, and this module proves it: at
the cyclic subgroups `⟨h₀⟩`, `⟨h₁⟩` the clause follows from independence alone,
by `GGT.Elementary.not_independent_of_common_zpow`.  An element of both is
`h₀^p = h₁^q`, and if it is not the identity then neither exponent is zero, so
the two elements are not independent.

What the clause still costs is therefore exactly the first half of the sentence:
that the subgroups Hull's §5 produces *are* the cyclic ones, which over a
torsion-free ambient group is `E(hᵢ) = ⟨hᵢ⟩` and in general is not true --- with
torsion, `E(h₀) ∩ E(h₁)` contains the maximal finite normal subgroup of `G`,
which a suitable `N` makes trivial only because it normalises it.  So a citation
stated at arbitrary subgroups has to carry (W4), and a citation stated at the
cyclic ones does not.

Nothing here changes `ExistsHypEmbeddedConeOff₂`; changing it is the owner's
call, and this module is the evidence for the choice.
-/

namespace GroupApproximation
namespace GGT
namespace Elementary

open GroupApproximation.HullGeometry

universe u v

variable {G : Type u} [Group G] {X : Type v} [PseudoMetricSpace X] [MulAction G X]

/-- **Independent loxodromics generate cyclic subgroups that meet trivially.**

This is Hull's (W4) for the cyclic choice.  A common element is `h₀ ^ p = h₁ ^ q`
with both exponents nonzero as soon as it is nontrivial, and
`not_independent_of_common_zpow` turns that into a failure of independence. -/
theorem eq_one_of_mem_zpowers_of_mem_zpowers_of_independent
    (hiso : IsIsometricAction G X) {h₀ h₁ : G} {x : X}
    (hlox : IsLoxodromic h₀ x) (hind : Independent h₀ h₁ x) (y : G)
    (hy₀ : y ∈ Subgroup.zpowers h₀) (hy₁ : y ∈ Subgroup.zpowers h₁) : y = 1 := by
  by_contra hy
  obtain ⟨p, hp⟩ := Subgroup.mem_zpowers_iff.mp hy₀
  obtain ⟨q, hq⟩ := Subgroup.mem_zpowers_iff.mp hy₁
  have hp0 : p ≠ 0 := by
    intro h0
    rw [h0, zpow_zero] at hp
    exact hy hp.symm
  have hq0 : q ≠ 0 := by
    intro h0
    rw [h0, zpow_zero] at hq
    exact hy hq.symm
  exact not_independent_of_common_zpow hiso hlox hp0 hq0 (hp.trans hq.symm) hind

/-- The same, in the form the pair statement asks for: the two cyclic subgroups
of a pair of independent loxodromics intersect trivially. -/
theorem zpowers_disjoint_of_independent (hiso : IsIsometricAction G X)
    {h : Bool → G} {x : X} (hlox : IsLoxodromic (h false) x)
    (hind : Independent (h false) (h true) x) :
    ∀ y : G, y ∈ Subgroup.zpowers (h false) → y ∈ Subgroup.zpowers (h true) →
      y = 1 :=
  eq_one_of_mem_zpowers_of_mem_zpowers_of_independent hiso hlox hind

end Elementary
end GGT
end GroupApproximation
