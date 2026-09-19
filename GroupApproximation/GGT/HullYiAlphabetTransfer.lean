import GroupApproximation.Manuscript.NonMF.AcylindricallyHyperbolic

/-!
# Hull's Lemma A.1: loxodromy comes back down from an enlarged alphabet

M. Hull, *Small cancellation in acylindrically hyperbolic groups*, Lemma A.1.

> Suppose `τ(h) > 0` with respect to the action of `G` on `Γ(G, 𝒜₁)`, and
> `𝒜 ⊆ 𝒜₁` generates `G`.  Then `τ(h) > 0` with respect to the action of `G` on
> `Γ(G, 𝒜)`.

His proof is one line --- `lim (1/n) d_𝒜(x, hⁿx) ≥ lim (1/n) d_{𝒜₁}(x, hⁿx) > 0`
--- and this module is that line, in the repository's `IsLoxodromic`
vocabulary rather than through stable translation lengths: enlarging the
alphabet cannot lengthen a word (`WordMetric.wordNorm_mono`), so the linear
lower bound over the larger alphabet is a linear lower bound over the smaller
one with the same constants.  Nothing is lost by avoiding `stableTranslation`:
`IsLoxodromic` is already the linear-lower-bound form, which is what the
inequality bounds.

## Why it is needed

It is the last step of Hull's **Lemma `yi`**, the manufacture of loxodromic
elements whose elementary closure is exactly cyclic.  That construction runs on
the enlarged alphabet `𝒜₁ = 𝒜 ⊔ E(f₁) ⊔ … ⊔ E(f_k)`, where the elementary
closures have been coned off, and produces elements loxodromic **there**.  What
Hull's Corollary `suitsubc` --- and therefore
`HullSC.ExistsHypEmbeddedConeOff₂` --- asserts is loxodromy on `Γ(G, 𝒜)`, the
prescribed alphabet.  This lemma is the passage between them.

The direction matters and is easy to get backwards.  Loxodromy transfers
**down** to the smaller alphabet, never up: over the larger alphabet distances
are smaller, so a linear lower bound there is the stronger statement.  Coning
off can only make elements elliptic, never loxodromic --- which is
`GGT.RelGenSet.not_isLoxodromic_of_mem_fam` for the elements of the coned-off
family itself.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

/-- **Enlarging the alphabet cannot increase the displacement of the
basepoint.**  The two sides are word lengths of the same element over the two
alphabets, and `WordMetric.wordNorm_mono` compares them. -/
theorem dist_base_le_of_subset {G : Type u} [Group G] {A A₁ : Alphabet G}
    (hAA : A.carrier ⊆ A₁.carrier) (g : G) :
    dist (Cayley.base A₁) (g • Cayley.base A₁)
      ≤ dist (Cayley.base A) (g • Cayley.base A) := by
  simp only [Cayley.dist_eq, Cayley.val_base, Cayley.val_smul, mul_one,
    wordDist_one_left]
  exact_mod_cast wordNorm_mono hAA (wordLengths_nonempty A.symmetricGenerating g)

/-- **Hull, Lemma A.1.**  An element loxodromic on the Cayley graph of the
larger alphabet is loxodromic on the Cayley graph of the smaller one, with the
same constants. -/
theorem isLoxodromic_base_of_subset {G : Type u} [Group G] {A A₁ : Alphabet G}
    (hAA : A.carrier ⊆ A₁.carrier) {g : G}
    (hlox : IsLoxodromic g (Cayley.base A₁)) :
    IsLoxodromic g (Cayley.base A) := by
  obtain ⟨l, hl, C, hC, hle⟩ := hlox
  exact ⟨l, hl, C, hC, fun n => le_trans (hle n) (dist_base_le_of_subset hAA (g ^ n))⟩

/-- The same for a family, which is the form `yi` hands to `suitsubc`: the
manufactured elements are produced loxodromic on `Γ(G, 𝒜₁)` and consumed
loxodromic on `Γ(G, 𝒜)`. -/
theorem isLoxodromic_base_of_subset_family {G : Type u} [Group G]
    {A A₁ : Alphabet G} (hAA : A.carrier ⊆ A₁.carrier) {ι : Type*} {g : ι → G}
    (hlox : ∀ i, IsLoxodromic (g i) (Cayley.base A₁)) :
    ∀ i, IsLoxodromic (g i) (Cayley.base A) :=
  fun i => isLoxodromic_base_of_subset hAA (hlox i)

end HullSC
end GroupApproximation
