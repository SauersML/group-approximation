import GroupApproximation.GGT.HullSCTheorem51

/-!
# Hull's §5 leaf, with the bookkeeping removed

**Superseded, and not merely unused.**  `Manuscript.NonMF.TheoremCAssembly` records
Hull's §5 leaf over a **pair** of hyperbolically embedded subgroups
(`HullSC.ExistsHypEmbeddedConeOff₂`, in
`GGT/HullSCRelatorSeparation2ConeOff.lean`), because the single-subgroup form
below cannot carry Hull's relator: over one `H` all of the relator's `H`-letters
lie in one component of `Γ(G, X ⊔ H)`, so the word runs between vertices at
distance at most one and is not quasi-geodesic
(`HullSC.not_quasiGeodesic_relatorWord`), which his §5 requires it to be.  With
two subgroups the relator alternates between the components
(`HullSC.isComp_relatorWord₂`).

What is below stays because it is true and because the pair form is its
verbatim analogue --- `HullSC.HypEmbeddedCore₂.ofConeOff` is
`HypEmbeddedCore.ofConeOff` with `Bool` for `Unit` --- so the reasoning here is
the reasoning there.  Nothing on the trust surface consumes it.

`HullSC.ExistsHypEmbeddedInSuitable` -- Hull, Corollary 5.7 with Lemma 5.8, in
the form Theorem 5.1 consumes it -- is stated over `HullSC.HypEmbeddedCore`,
which carries a relative generating set together with two equations pinning its
base to Hull's alphabet and its family to the subgroup.  None of that is
content: `HullSC.coneOff` is *the* relative generating set with that base and
that family, and `GGT.RelGenSet.alphabet` of it is Osin's `X ⊔ H`.

So the leaf is equivalent to a plain existential over subgroups:

> there is `H ≤ N` with `Γ(G, A ⊔ H)` hyperbolic and `H` carrying a locally
> finite relative metric -- that is, `(coneOff A H).IsHyperbolicallyEmbedded` --
> and with an element of `H` loxodromic on `Γ(G,A)`.

`ExistsHypEmbeddedConeOff` is that statement and
`existsHypEmbeddedInSuitable_of_coneOff` derives the structured form from it,
through the constructor `HypEmbeddedCore.ofConeOff`, whose two equation fields
are `rfl`.  Whoever discharges Hull's §5 therefore owes three conditions on one
subgroup and nothing else.

The loxodromic clause is not decoration and is not dropped here: without it the
statement is satisfied by `H = ⊥`, and `HullSC.HypEmbeddedCore.not_subset`
turns it into `H ⊄ A`, which is what keeps
`GGT.not_isHypEmbeddedOf_of_subset` -- a subgroup inside its own base is never
hyperbolically embedded over it -- from refuting the embedding clause.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

/-- **The core, from the cone-off.**  The relative generating set is
`coneOff A.alphabet K`, whose base is Hull's alphabet and whose family is `K`
by definition, so both equation fields are `rfl`. -/
def HypEmbeddedCore.ofConeOff {G : Type u} [Group G] {A : HullGeneratingSet G}
    {N : Subgroup G} (K : Subgroup G) (hle : K ≤ N)
    (hemb : (coneOff A.alphabet K).IsHyperbolicallyEmbedded) (g : G)
    (hgK : g ∈ K) (hglox : IsLoxodromic g (Cayley.base A.alphabet)) :
    HypEmbeddedCore A N where
  rel := coneOff A.alphabet K
  base_eq := rfl
  H := K
  fam_eq := rfl
  le := hle
  embedded := hemb
  lox := g
  lox_mem := hgK
  lox_isLoxodromic := hglox

/-- **Hull, Corollary 5.7 with Lemma 5.8, in the minimal form.**  A suitable
subgroup contains a subgroup whose cone-off over Hull's alphabet is
hyperbolically embedded and which contains an element loxodromic on
`Γ(G,A)`. -/
def ExistsHypEmbeddedConeOff : Prop :=
  ∀ {G : Type u} [Group G] (A : HullGeneratingSet G) {N : Subgroup G},
    Suitable A.alphabet N →
      ∃ K : Subgroup G, K ≤ N ∧
        (coneOff A.alphabet K).IsHyperbolicallyEmbedded ∧
          ∃ g ∈ K, IsLoxodromic g (Cayley.base A.alphabet)

/-- The structured leaf follows from the plain one: the structure adds
bookkeeping, not hypotheses. -/
theorem existsHypEmbeddedInSuitable_of_coneOff
    (h : ExistsHypEmbeddedConeOff.{u}) : ExistsHypEmbeddedInSuitable.{u} := by
  intro G _ A N hN
  obtain ⟨K, hle, hemb, g, hgK, hglox⟩ := h A hN
  exact ⟨HypEmbeddedCore.ofConeOff K hle hemb g hgK hglox⟩

/-- **A relative generating set is its base and its family.**  The third field
is a `Prop`, so proof irrelevance closes the equality once the other two agree.
This is what makes the bookkeeping of `HypEmbeddedCore` inert. -/
theorem relGenSet_eq {G : Type u} [Group G] {Λ : Type*}
    {D D' : GGT.RelGenSet G Λ} (hb : D.base = D'.base) (hf : D.fam = D'.fam) :
    D = D' := by
  obtain ⟨b, f, hsg⟩ := D
  obtain ⟨b', f', hsg'⟩ := D'
  have hb' : b = b' := hb
  have hf' : f = f' := hf
  subst hb'
  subst hf'
  rfl

/-- And conversely the plain leaf follows from the structured one, so nothing
has been strengthened and the two are the same citation: `E.base_eq` and
`E.fam_eq` identify `E.rel` with the cone-off, by `relGenSet_eq`. -/
theorem existsHypEmbeddedConeOff_of_core (h : ExistsHypEmbeddedInSuitable.{u}) :
    ExistsHypEmbeddedConeOff.{u} := by
  intro G _ A N hN
  obtain ⟨E⟩ := h A hN
  have hrel : E.rel = coneOff A.alphabet E.H := by
    refine relGenSet_eq ?_ ?_
    · show E.rel.base = A.alphabet.carrier
      exact E.base_eq
    · show E.rel.fam = fun _ => E.H
      exact E.fam_eq
  refine ⟨E.H, E.le, ?_, E.lox, E.lox_mem, E.lox_isLoxodromic⟩
  rw [← hrel]
  exact E.embedded

end HullSC
end GroupApproximation
