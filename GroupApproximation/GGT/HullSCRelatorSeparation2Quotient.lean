import GroupApproximation.GGT.HullSCRelatorSeparation2Assembly
import GroupApproximation.GGT.HullSCDGO

/-!
# Hull's Theorem 5.1 over two subgroups, closed to three inputs

`HullSC.hullQuotient_of_fillingData` derives Hull's Theorem 5.1 from
Dahmani--Guirardel--Osin's Theorem 5.3 and the family Hull builds, and its proof
mentions no index type: it works with rotating data, a `RotatingQuotient` and
a `FillingAlphabetData`, none of which is indexed.  So it transfers to the
two-subgroup setting, and only the statement it consumes has to be restated.

`HullFillingDataStatement₂` is that statement and `hullQuotient₂_of_fillingData`
the transfer; `HullConeOffStatement₂` is Hull's §5 for a pair, and
`hullFillingDataStatement₂_of_coneOff` derives the family from it through
`HullSC.ConeOffData₂.toRotatingDataGeo`.  Composing with the relator half of
`GGT/HullSCRelatorSeparation2Statement.lean`,
`hullTheorem51₂_of_separationNe₂_of_coneOff` puts Hull's Theorem 5.1 over two
subgroups on exactly three inputs:

* the corrected separation -- Olshanskii's estimate with `w' ≠ w` restored,
* `HullConeOffStatement₂` -- Hull's §5, that the cone-off along a pair exists,
* `DGOQuotientStatementGeodesic` -- DGO's Theorem 5.3 in its repaired form.

The third is the geodesic statement and not `HullSC.DGOQuotientStatement`,
which `GGT/HullSCDGO.lean` refutes: with no geodesic the very rotating
condition constrains an annulus that can be empty.  So the cone-off is asked
for a geodesic, and `HullSC.RotatingDataGeo₂` carries it.

The last two inputs are citations.  Everything between them is proved: the
alternating relator and its component structure, the exponent design, block
rigidity, the family cone-off, the rotating family with its three axioms, what
the rotations generate, the injectivity of the quotient on the ball, and the
assembly into the rotating data.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

/-- **The family Hull's §5 builds, over two subgroups.**

Both halves are quantified over the same parameters, which is what keeps them
from drifting: the alphabet clause is false for an arbitrary quotient by an
arbitrary element, so it may not be stated before the small cancellation
condition that pins the relator down. -/
def HullFillingDataStatement₂ : Prop :=
  ∀ {G : Type u} [Group G] (A : HullGeneratingSet G) (N : Subgroup G)
    (E : HypEmbeddedCore₂ A N), Suitable A.alphabet N →
      ∀ {k : ℕ} (S : Fin k → Subgroup G),
        (∀ j : Fin k, Suitable A.alphabet (S j)) → ∀ R : ℕ,
          ∃ (eps rho : ℕ) (mu : ℝ), 0 < mu ∧
            ∀ (W : Set (List (GGT.RelLetter G Bool)))
              (v : List (GGT.RelLetter G Bool)), v ∈ W →
              RelWord.IsSmallCancellation E.rel W eps mu rho →
                Nonempty (RotatingDataGeo₂ A.alphabet (GGT.RelLetter.listVal v)
                    (2 * (R : ℝ))) ∧
                  ∀ {Q : Type u} [Group Q] (q : G →* Q), Function.Surjective q →
                    q.ker = Subgroup.normalClosure
                        ({GGT.RelLetter.listVal v} : Set G) →
                      Nonempty (FillingAlphabetData A N S q)

/-- **Hull's Theorem 5.1 over two subgroups, from DGO's Theorem 5.3 and the
family.**

Seven of the ten fields of `HullFillingQuotient` come out of the rotating
quotient, injectivity on the ball comes from
`RotatingDataGeo₂.kernel_moves_base` through `RotatingDataGeo₂.injOn_cayleyBall`,
and the remaining three are the alphabet clauses.  Nothing in it mentions the
index type. -/
theorem hullQuotient₂_of_fillingData
    (hDGO : DGOQuotientStatementGeodesic.{u, u})
    (hdata : HullFillingDataStatement₂.{u}) : HullQuotientStatement₂.{u} := by
  intro G _ A N E hN k S hS R
  obtain ⟨eps, rho, mu, hmu, hgood⟩ := hdata A N E hN S hS R
  refine ⟨eps, rho, mu, hmu, ?_⟩
  intro W v hv hsc
  obtain ⟨⟨D⟩, halph⟩ := hgood W v hv hsc
  obtain ⟨P⟩ := hDGO D.delta D.sep D.apices D.rot D.delta_pos D.sep_ge
    D.hyperbolic D.isGeodesic D.isRotatingFamily D.isSeparated D.isVeryRotating
  have hker : P.q.ker
      = Subgroup.normalClosure ({GGT.RelLetter.listVal v} : Set G) := by
    rw [P.ker_eq, D.rotationNormalClosure_eq]
  obtain ⟨F⟩ := halph P.q P.surjective hker
  exact ⟨{ Q := P.Q
           group := P.group
           q := P.q
           surjective := P.surjective
           ker_eq := hker
           hullSet := F.hullSet
           alphabet_image := F.alphabet_image
           injOn := D.injOn_cayleyBall P.q hker
           suitable_map := F.suitable_map
           suitable_map_family := F.suitable_map_family
           finiteOrder_lift := P.finiteOrder_lift }⟩

/-- **Hull's §5 over two subgroups: the cone-off exists.**

The family of rotation subgroups is existentially quantified rather than named,
because which subgroups the construction produces is Hull's to say and not
something to guess: what the consumer needs of them is only that their normal
closure is the normal closure of the relator, which is the clause carried here.

What the cone-off is asked for is exactly `HullSC.ConeOffData₂`: a hyperbolic
**geodesic** space with one apex per member of the family, the apices separated
and their orbits disjoint, the rotations very rotating, and an injectivity
radius above `2R` at the basepoint.  The geodesic is not decoration: the
repaired form of DGO's Theorem 5.3 asks for it, and Hull's cone-off has it. -/
def HullConeOffStatement₂ : Prop :=
  ∀ {G : Type u} [Group G] (A : HullGeneratingSet G) (N : Subgroup G)
    (E : HypEmbeddedCore₂ A N), Suitable A.alphabet N →
      ∀ {k : ℕ} (S : Fin k → Subgroup G),
        (∀ j : Fin k, Suitable A.alphabet (S j)) → ∀ R : ℕ,
          ∃ (eps rho : ℕ) (mu : ℝ), 0 < mu ∧
            ∀ (W : Set (List (GGT.RelLetter G Bool)))
              (v : List (GGT.RelLetter G Bool)), v ∈ W →
              RelWord.IsSmallCancellation E.rel W eps mu rho →
                (∃ (K : Bool → Subgroup G)
                    (_ : ConeOffData₂ A.alphabet K (2 * (R : ℝ))),
                    Subgroup.normalClosure (⋃ b : Bool, (K b : Set G))
                      = Subgroup.normalClosure
                          ({GGT.RelLetter.listVal v} : Set G)) ∧
                  ∀ {Q : Type u} [Group Q] (q : G →* Q), Function.Surjective q →
                    q.ker = Subgroup.normalClosure
                        ({GGT.RelLetter.listVal v} : Set G) →
                      Nonempty (FillingAlphabetData A N S q)

/-- **Hull's §5 over two subgroups, from the cone-off.**
`ConeOffData₂.toRotatingDataGeo` supplies the rotating family, and the one
thing it needs -- what the family kills -- is the clause the cone-off statement
carries. -/
theorem hullFillingDataStatement₂_of_coneOff (h : HullConeOffStatement₂.{u}) :
    HullFillingDataStatement₂.{u} := by
  intro G _ A N E hN k S hS R
  obtain ⟨eps, rho, mu, hmu, hgood⟩ := h A N E hN S hS R
  refine ⟨eps, rho, mu, hmu, ?_⟩
  intro W v hv hsc
  obtain ⟨⟨K, P, hclosure⟩, halph⟩ := hgood W v hv hsc
  exact ⟨⟨P.toRotatingDataGeo (GGT.RelLetter.listVal v) hclosure⟩, halph⟩

/-- **Hull's Theorem 5.1 proper over two subgroups, from the cone-off and DGO's
Theorem 5.3.** -/
theorem hullQuotientStatement₂_of_coneOff
    (hcone : HullConeOffStatement₂.{u})
    (hDGO : DGOQuotientStatementGeodesic.{u, u}) : HullQuotientStatement₂.{u} :=
  hullQuotient₂_of_fillingData hDGO (hullFillingDataStatement₂_of_coneOff hcone)

/-- **Hull's Theorem 5.1 over two subgroups, on three inputs.**

The corrected separation, DGO's Theorem 5.3 in its repaired form, and the
family of Hull's §5.  Everything else this lane needed -- the alternating
relator, its component structure, the exponent design, block rigidity, the
family cone-off, the rotating family and its three axioms, what the rotations
generate, and the assembly into the rotating data -- is proved. -/
theorem hullTheorem51₂_of_separationNe₂_of_coneOff
    (hsep : ∀ {G : Type u} [Group G] (A : HullGeneratingSet G) (N : Subgroup G)
      (E : HypEmbeddedCore₂ A N), Suitable A.alphabet N →
        ∀ (t : G) (eps rho : ℕ), ∃ B : ℕ, ∀ L : ℕ,
          ∃ (p : List G) (ms : List ℕ),
            (∀ g ∈ p, g ∈ E.rel.base) ∧ p.prod = t⁻¹ ∧ L ≤ ms.length ∧
              (∀ m ∈ ms, ∀ b : Bool, E.lox b ^ m ∉ E.rel.relBall b rho ∧
                (E.lox b ^ m)⁻¹ ∉ E.rel.relBall b rho) ∧
              ∀ w w' u₀ u₀' : List (GGT.RelLetter G Bool),
                RelWord.Sym (relatorWord₂ p (E.lox false) (E.lox true) ms) w →
                  RelWord.Sym (relatorWord₂ p (E.lox false) (E.lox true) ms) w' →
                    w' ≠ w → (∃ s, w = u₀ ++ s) → (∃ s', w' = u₀' ++ s') →
                      B < u₀.length →
                        ∀ y z : G, wordNorm E.rel.base y ≤ eps →
                          wordNorm E.rel.base z ≤ eps →
                            GGT.RelLetter.listVal u₀'
                                = y * GGT.RelLetter.listVal u₀ * z →
                              GGT.RelLetter.listVal w'
                                = y * GGT.RelLetter.listVal w * y⁻¹)
    (hcone : HullConeOffStatement₂.{u})
    (hDGO : DGOQuotientStatementGeodesic.{u, u}) :
    HullTheorem51Statement₂.{u} :=
  hullTheorem51₂_of_relator_of_quotient
    (hullRelatorStatement₂_of_separationNe₂ hsep)
    (hullQuotientStatement₂_of_coneOff hcone hDGO)

end HullSC
end GroupApproximation
