import GroupApproximation.GGT.HullSCRelatorSeparation2QuasiGeodesic
import GroupApproximation.GGT.HullSCCoreAdjoinPair

/-!
# Hull's Theorem 5.1 over two subgroups, and its two halves

`HullSC.HullTheorem51Statement` and `HullSC.HullQuotientStatement` are written at
`GGT.RelLetter G Unit`, but the type only enters through
`RelWord.IsSmallCancellation E.rel W eps mu rho`, and that is already stated for
an arbitrary index type.  `HullSC.HullFillingQuotient` -- the output of the
theorem -- mentions no index type at all: it is data about the quotient group,
the quotient map, the alphabet of the quotient and the suitability of the
images.

So the Theorem 5.1 layer generalises for free, and the two statements below are
the same statements over `HullSC.HypEmbeddedCore₂`.  What does *not* generalise
for free is their proof: `HullSC.HullConeOffStatement` and the rotating-family
chain under it build one cone-off along one subgroup, and coning off a family
is a genuine generalisation of that construction rather than a retyping.

`hullTheorem51₂_of_relator_of_quotient` is the composition, and it is the same
seam as over one subgroup: the parameters come out of the quotient half and go
into the relator half, which is the direction Hull's proof runs.  With
`HullSC.hullRelatorStatement₂_of_separationNe₂` the relator half is discharged
down to Olshanskii's separation, so what is left of Hull's Theorem 5.1 over two
subgroups is the quotient half alone.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

/-- **Hull, Theorem 5.1 proper, over two subgroups.**

> Let `G` be acylindrically hyperbolic with Hull's alphabet `A`, let `N` be
> suitable, let `{H₀, H₁} ↪_h (G, A)` with independent loxodromic elements, let
> `S₁, …, S_k` be suitable and let `R` be a radius.  Then there are `eps, mu,
> rho` such that for every family `W` satisfying `C(eps, mu, rho)` over
> `{H₀, H₁}` and every `w ∈ W`, the quotient by the normal closure of what `w`
> spells has the filling properties.

The parameters are produced before the family, which is the direction Hull's
proof runs and what lets the relator be chosen afterwards. -/
def HullQuotientStatement₂ : Prop :=
  ∀ {G : Type u} [Group G] (A : HullGeneratingSet G) (N : Subgroup G)
    (E : HypEmbeddedCore₂ A N), Suitable A.alphabet N →
      ∀ {k : ℕ} (S : Fin k → Subgroup G),
        (∀ j : Fin k, Suitable A.alphabet (S j)) → ∀ R : ℕ,
          ∃ (eps rho : ℕ) (mu : ℝ), 0 < mu ∧
            ∀ (W : Set (List (GGT.RelLetter G Bool)))
              (v : List (GGT.RelLetter G Bool)), v ∈ W →
              RelWord.IsSmallCancellation E.rel W eps mu rho →
                Nonempty (HullFillingQuotient A N S (GGT.RelLetter.listVal v) R)

/-- **Hull's Theorem 5.1 with the §6 relator, over two subgroups.** -/
def HullTheorem51Statement₂ : Prop :=
  ∀ {G : Type u} [Group G] (A : HullGeneratingSet G) (N : Subgroup G),
    HypEmbeddedCore₂ A N → Suitable A.alphabet N →
      ∀ {k : ℕ} (S : Fin k → Subgroup G),
        (∀ j : Fin k, Suitable A.alphabet (S j)) → ∀ (t : G) (R : ℕ),
          ∃ u ∈ N, Nonempty (HullFillingQuotient A N S (t⁻¹ * u) R)

/-- **Hull's Theorem 5.1 over two subgroups, from its two halves.**

Nothing is lost in the seam: both statements are quantified over
`RelWord.IsSmallCancellation` as defined in `GGT/HullSCSmallCancellation.lean`,
which is stated for an arbitrary index type, so the citation and its consumer
cannot drift apart. -/
theorem hullTheorem51₂_of_relator_of_quotient
    (hrel : HullRelatorStatement₂.{u}) (hquot : HullQuotientStatement₂.{u}) :
    HullTheorem51Statement₂.{u} := by
  intro G _ A N E hN k S hS t R
  obtain ⟨eps, rho, mu, hmu, hgood⟩ := hquot A N E hN S hS R
  obtain ⟨u, huN, W, ⟨v, hvW, hvval⟩, hsc⟩ := hrel A N E hN t eps rho mu hmu
  refine ⟨u, huN, ?_⟩
  have hq := hgood W v hvW hsc
  rwa [hvval] at hq

/-- **Hull's Theorem 5.1 over two subgroups, from the BASE-LETTER relator half.**

The seam where the alphabet is enlarged, and the only place it needs to be.
`HullRelatorStatement₂OfBaseLetter` asks its core to carry `t⁻¹` as a base
letter, which no core handed in need satisfy --- so this proof adjoins one:
`HypEmbeddedCore₂.adjoinPair` puts `t` and `t⁻¹` into the base and carries the
other clauses over unchanged, and `mem_base_adjoinPair` is the hypothesis.

Adjoining is free HERE and nowhere else, for a reason visible in the statement:
`HullTheorem51Statement₂`'s conclusion is
`∃ u ∈ N, Nonempty (HullFillingQuotient A N S (t⁻¹ * u) R)`, which does not
mention the core at all.  So the enlarged core may be used throughout the proof
and never escapes it, and no consumer of this theorem changes.  `t` is in scope
before the core is used, which is what makes the enlargement possible at all;
at `HullRelatorStatement₂OfBaseLetter` itself the core comes first and the
adjunction could not be expressed.

Both halves are instantiated at the SAME enlarged core.  The quotient half's
`hgood` consumes small-cancellation data over the core it was given, so taking
it at `E` while the relator half runs at `E.adjoinPair t` would not typecheck
--- the two must agree, and they do. -/
theorem hullTheorem51₂_of_relatorBaseLetter_of_quotient
    (hrel : HullRelatorStatement₂OfBaseLetter.{u})
    (hquot : HullQuotientStatement₂.{u}) :
    HullTheorem51Statement₂.{u} := by
  intro G _ A N E hN k S hS t R
  obtain ⟨eps, rho, mu, hmu, hgood⟩ := hquot A N (E.adjoinPair t) hN S hS R
  obtain ⟨u, huN, W, ⟨v, hvW, hvval⟩, hsc⟩ :=
    hrel A N (E.adjoinPair t) hN t (mem_base_adjoinPair E t) eps rho mu hmu
  refine ⟨u, huN, ?_⟩
  have hq := hgood W v hvW hsc
  rwa [hvval] at hq

/-- **Hull's Theorem 5.1 over two subgroups, from the corrected separation and
the quotient half.**  The relator half is `hullRelatorStatement₂_of_separationNe₂`,
so this is the composite of everything this lane proves with the one half it
does not. -/
theorem hullTheorem51₂_of_separationNe₂_of_quotient
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
                        ∀ y z : G, wordNorm E.rel.alphabet.carrier y ≤ eps →
                          wordNorm E.rel.alphabet.carrier z ≤ eps →
                            GGT.RelLetter.listVal u₀'
                                = y * GGT.RelLetter.listVal u₀ * z →
                              GGT.RelLetter.listVal w'
                                = y * GGT.RelLetter.listVal w * y⁻¹)
    (hquot : HullQuotientStatement₂.{u}) : HullTheorem51Statement₂.{u} :=
  hullTheorem51₂_of_relator_of_quotient
    (hullRelatorStatement₂_of_separationNe₂ hsep) hquot

end HullSC
end GroupApproximation
