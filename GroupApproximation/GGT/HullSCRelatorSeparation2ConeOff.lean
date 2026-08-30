import GroupApproximation.GGT.HullSCRelatorSeparation2Theorem51

/-!
# Coning off a family

`HullSC.coneOff` adjoins one subgroup to Hull's alphabet and produces a
`GGT.RelGenSet G Unit`.  Hull's Theorem 5.1 is run over a *family*, and
`GGT/HullSCRelatorSeparationNotQG.lean` shows why the single-subgroup version
cannot carry his relator, so the construction has to be done for a family.

`coneOffFamily A K` is that: the same base, the family `K` itself as the family,
and the same generation argument -- adjoining letters to a generating set leaves
it generating, and both a symmetric alphabet and a subgroup are closed under
inversion.  Nothing about it depends on the index type being `Unit`, which is
why the single-subgroup version was never the general one.

`HypEmbeddedCore₂.ofConeOff` builds the two-subgroup core from it, and its two
equation fields are `rfl`, exactly as over one subgroup.  So
`ExistsHypEmbeddedConeOff₂` -- Hull's Corollary 5.7 with Lemma 5.8, for a pair
of independent loxodromics -- is a plain existential over pairs of subgroups,
and whoever discharges Hull's §5 owes four conditions on two subgroups and
nothing else.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w

/-- **The cone-off along a family.**  The base is the alphabet and the family is
the given one; adjoining the subgroups to a generating set leaves it generating,
and the union is symmetric because the alphabet is and each subgroup is. -/
def coneOffFamily {G : Type u} [Group G] {Λ : Type w} (A : Alphabet G)
    (K : Λ → Subgroup G) : GGT.RelGenSet G Λ where
  base := A.carrier
  fam := K
  symmetricGenerating := by
    refine ⟨?_, ?_⟩
    · intro x hx
      rcases hx with hx | hx
      · exact Or.inl (A.symmetricGenerating.inv_mem x hx)
      · obtain ⟨lam, hxlam⟩ := Set.mem_iUnion.mp hx
        exact Or.inr (Set.mem_iUnion.mpr ⟨lam, (K lam).inv_mem hxlam⟩)
    · refine eq_top_iff.mpr ?_
      rw [← A.symmetricGenerating.closure_eq]
      exact Subgroup.closure_mono Set.subset_union_left

@[simp] theorem coneOffFamily_base {G : Type u} [Group G] {Λ : Type w}
    (A : Alphabet G) (K : Λ → Subgroup G) :
    (coneOffFamily A K).base = A.carrier := rfl

@[simp] theorem coneOffFamily_fam {G : Type u} [Group G] {Λ : Type w}
    (A : Alphabet G) (K : Λ → Subgroup G) : (coneOffFamily A K).fam = K := rfl

/-! ## The two-subgroup core from the cone-off -/

/-- **The two-subgroup core, from the cone-off along the pair.**  Both equation
fields are `rfl`, so the structure adds bookkeeping and not hypotheses. -/
def HypEmbeddedCore₂.ofConeOff {G : Type u} [Group G] {A : HullGeneratingSet G}
    {N : Subgroup G} (K : Bool → Subgroup G) (hle : ∀ b : Bool, K b ≤ N)
    (hemb : (coneOffFamily A.alphabet K).IsHyperbolicallyEmbedded)
    (g : Bool → G) (hgK : ∀ b : Bool, g b ∈ K b)
    (hglox : ∀ b : Bool, IsLoxodromic (g b) (Cayley.base A.alphabet))
    (hind : Independent (g false) (g true) (Cayley.base A.alphabet))
    (hdisj : ∀ x : G, x ∈ K false → x ∈ K true → x = 1) :
    HypEmbeddedCore₂ A N where
  rel := coneOffFamily A.alphabet K
  base_eq := rfl
  H := K
  fam_eq := rfl
  le := hle
  embedded := hemb
  lox := g
  lox_mem := hgK
  lox_isLoxodromic := hglox
  lox_independent := hind
  disjoint := hdisj

/-- **Hull, Corollary 5.7 with Lemma 5.8, for a pair.**

> A suitable subgroup contains two subgroups whose cone-off over Hull's alphabet
> is hyperbolically embedded and which contain independent loxodromic elements.

The independence clause is what puts the two elements in different members of
the family, and so is what keeps consecutive letters of Hull's relator in
different components (`HullSC.isComp_relatorWord₂`).  Without it the pair
degenerates to the single-subgroup case that
`HullSC.not_quasiGeodesic_relatorWord` refutes.

The last clause is Hull's (W4), that the two subgroups meet trivially.  It is
part of what §5 delivers --- Corollary 5.7 gives `E(hᵢ) = ⟨hᵢ⟩` and
independence separates them --- and it is recorded in the citation rather than
derived here; `HullSC.HypEmbeddedCore₂.disjoint` carries it downstream. -/
def ExistsHypEmbeddedConeOff₂ : Prop :=
  ∀ {G : Type u} [Group G] (A : HullGeneratingSet G) {N : Subgroup G},
    Suitable A.alphabet N →
      ∃ K : Bool → Subgroup G, (∀ b : Bool, K b ≤ N) ∧
        (coneOffFamily A.alphabet K).IsHyperbolicallyEmbedded ∧
          ∃ g : Bool → G, (∀ b : Bool, g b ∈ K b) ∧
            (∀ b : Bool, IsLoxodromic (g b) (Cayley.base A.alphabet)) ∧
              Independent (g false) (g true) (Cayley.base A.alphabet) ∧
                ∀ x : G, x ∈ K false → x ∈ K true → x = 1

/-- **The structured leaf follows from the plain one**, through
`HypEmbeddedCore₂.ofConeOff`. -/
theorem nonempty_hypEmbeddedCore₂_of_coneOff (h : ExistsHypEmbeddedConeOff₂.{u})
    {G : Type u} [Group G] (A : HullGeneratingSet G) {N : Subgroup G}
    (hN : Suitable A.alphabet N) : Nonempty (HypEmbeddedCore₂ A N) := by
  obtain ⟨K, hle, hemb, g, hgK, hglox, hind, hdisj⟩ := h A hN
  exact ⟨HypEmbeddedCore₂.ofConeOff K hle hemb g hgK hglox hind hdisj⟩

end HullSC
end GroupApproximation
