import GroupApproximation.Manuscript.NonMF.HullSmallCancellation

/-!
# Hull's Theorem 7.1: from the ball form to the finite-set form

> *"Hull's small cancellation theorem [Hull, Theorem 7.1] is stated with
> injectivity on a ball of `Γ(G,A)`; a ball containing a given finite set
> gives the following form."*

Hull's published theorem produces, for a radius `R`, a quotient injective on
the closed `R`-ball of `Γ(G,A)` about the basepoint.  The manuscript records
the finite-set form.  The passage is two facts, both proved here: a finite
subset of `G` lies in some ball (`exists_subset_cayleyBall`, from
`exists_ball_containing`), and injectivity on a ball containing `F` gives
injectivity on `F` (`HullQuotient.mono`).  Together they turn the ball form
of the theorem, stated as `HullBallFormStatement`, into the finite-set form
`HullInputs.smallCancellation` records (`smallCancellation_of_ballForm`).
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TorsionFree

open GroupApproximation.HullGeometry

universe u

/-- The closed ball of radius `R` of `Γ(G,A)` about the basepoint, as a subset
of `G`. -/
def cayleyBall {G : Type u} [Group G] (A : Alphabet G) (R : ℕ) : Set G :=
  {x | dist (Cayley.base A) (Cayley.of A x) ≤ (R : ℝ)}

/-- **"a ball containing a given finite set"**: a finite subset of `G` lies
in some ball of `Γ(G,A)`. -/
theorem exists_subset_cayleyBall {G : Type u} [Group G] (A : Alphabet G)
    {F : Set G} (hF : F.Finite) : ∃ R : ℕ, F ⊆ cayleyBall A R := by
  obtain ⟨R, hR⟩ := exists_ball_containing A hF
  exact ⟨R, fun x hx => hR x hx⟩

/-- Injectivity on a ball containing `F` gives injectivity on `F`. -/
theorem injOn_of_injOn_cayleyBall {G : Type u} [Group G] {Q : Type*} (q : G → Q)
    {A : Alphabet G} {R : ℕ} {F : Set G} (hF : F ⊆ cayleyBall A R)
    (h : Set.InjOn q (cayleyBall A R)) : Set.InjOn q F :=
  h.mono hF

/-- A Hull quotient injective on a set is a Hull quotient injective on every
subset. -/
def HullQuotient.mono {G : Type u} [Group G] {N : Subgroup G} {m : ℕ}
    {t : Fin m → G} {F F' : Set G} (H : HullQuotient N t F') (hFF' : F ⊆ F') :
    HullQuotient N t F where
  Q := H.Q
  q := H.q
  surjective := H.surjective
  injOn := H.injOn.mono hFF'
  mem_map := H.mem_map
  finiteOrder_lift := H.finiteOrder_lift

/-- **Hull's Theorem 7.1 in its published form**: injectivity on the ball of
a given radius. -/
def HullBallFormStatement : Prop :=
  ∀ {G : Type u} [Group G] [IsAcylindricallyHyperbolic G]
    (A : HullGeneratingSet G) {N : Subgroup G}, Suitable A.alphabet N →
      ∀ {m : ℕ} (t : Fin m → G) (R : ℕ),
        Nonempty (HullQuotient N t (cayleyBall A.alphabet R))

/-- **"a ball containing a given finite set gives the following form"**: the
finite-set form of Hull's theorem, from the ball form. -/
theorem smallCancellation_of_ballForm (hball : HullBallFormStatement.{u}) :
    ∀ {G : Type u} [Group G] [IsAcylindricallyHyperbolic G]
      (A : HullGeneratingSet G) {N : Subgroup G}, Suitable A.alphabet N →
        ∀ {m : ℕ} (t : Fin m → G) {F : Set G}, F.Finite →
          Nonempty (HullQuotient N t F) := by
  intro G _ _ A N hN m t F hF
  obtain ⟨R, hR⟩ := exists_subset_cayleyBall A.alphabet hF
  obtain ⟨H⟩ := hball A hN t R
  exact ⟨H.mono hR⟩

end TorsionFree
end NonMF
end Manuscript
end GroupApproximation
