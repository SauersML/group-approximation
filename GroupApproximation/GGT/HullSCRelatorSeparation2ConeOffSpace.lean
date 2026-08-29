import GroupApproximation.GGT.HullSCRelatorSeparation2ConeOff

/-!
# The cone-off along a family, as the space Hull's Theorem 5.1 runs on

`HullSC.ConeOffData` carries one subgroup and one distinguished apex.  Hull's
Theorem 5.1 is run over a family, and `GGT/HullSCRelatorSeparationNotQG.lean`
shows why one subgroup cannot carry his relator, so the space has to carry one
apex per member of the family.

`ConeOffData₂` is that structure.  Every field of `HullSC.ConeOffData` appears,
indexed where the family indexes it:

* one apex per index, fixed by its own subgroup and normal in its own
  stabiliser;
* separation between *all* apices, across indices as well as within one orbit;
* the injectivity radius `injOn_of_dist`, against the normal closure of the
  whole family.

Two fields deserve comment.

`injOn_of_dist` is Hull's §5 and not DGO's Theorem 5.3, exactly as over one
subgroup: the free splitting and the dichotomy do not give an injectivity
radius, loxodromy is asymptotic and says nothing at the first power, and the
splitting is not metric.  It is mirrored here rather than claimed.

`apex_ne` is new, and it is the one clause a family needs that a single subgroup
does not: the orbits of the apices must not meet, or the rotation subgroup at a
shared point would have to be two different subgroups at once.  It is not
derivable from `separated`, which bounds the distance between apices that are
already known to differ and says nothing about whether they differ.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u v w

/-- **The cone-off along a family, with the data Theorem 5.1 consumes.**

`L` is the displacement below which the quotient has to be faithful.  As over
one subgroup, the lower bounds on the separation are all arranged the same way:
they are met by taking the relator deep enough. -/
structure ConeOffData₂ {G : Type u} [Group G] {Λ : Type w} (A : Alphabet G)
    (K : Λ → Subgroup G) (L : ℝ) where
  /-- The cone-off. -/
  Space : Type u
  /-- Its metric. -/
  [metric : PseudoMetricSpace Space]
  /-- The action of `G` on it. -/
  [action : MulAction G Space]
  /-- The action is by isometries. -/
  isometric : IsIsometricAction G Space
  /-- The basepoint, the image of the identity vertex of `Γ(G,A)`. -/
  base : Space
  /-- Every letter of `A` moves the basepoint by at most one. -/
  letter_dist : ∀ a ∈ A.carrier, dist base (a • base) ≤ 1
  /-- One apex per member of the family. -/
  apex : Λ → Space
  /-- Each rotation subgroup fixes its own apex. -/
  fix : ∀ (lam : Λ), ∀ k ∈ K lam, k • apex lam = apex lam
  /-- Each is normal in the stabiliser of its own apex. -/
  normal_in_stab : ∀ (lam : Λ) (s : G), s • apex lam = apex lam →
    ∀ k ∈ K lam, s * k * s⁻¹ ∈ K lam
  /-- **The orbits of the apices do not meet.**  Without it the rotation
  subgroup at a shared point would be two subgroups at once; it is not implied
  by `separated`, which speaks only of apices already known to differ. -/
  apex_ne : ∀ (lam mu : Λ), lam ≠ mu → ∀ g g' : G, g • apex lam ≠ g' • apex mu
  /-- The hyperbolicity constant. -/
  delta : ℝ
  /-- It is positive. -/
  delta_pos : 0 < delta
  /-- The cone-off is hyperbolic. -/
  hyperbolic : IsHyperbolicSpace delta Space
  /-- The separation of the apices. -/
  sep : ℝ
  /-- Dahmani-Guirardel-Osin's Theorem 5.3 asks for separation above `200 δ`. -/
  sep_ge : 200 * delta ≤ sep
  /-- The separation exceeds the prescribed displacement. -/
  lt_sep : L < sep
  /-- Distinct apices are `sep` apart, across indices as well as within one. -/
  separated : ∀ (lam mu : Λ) (g g' : G), g • apex lam ≠ g' • apex mu →
    sep ≤ dist (g • apex lam) (g' • apex mu)
  /-- The basepoint is `sep`-far from every apex. -/
  base_far : ∀ (lam : Λ) (g : G), sep ≤ dist base (g • apex lam)
  /-- **The injectivity radius, and it is Hull's §5 rather than DGO's.**
  Nothing that moves the basepoint by less than the separation is killed, for
  any quotient by the normal closure of the whole family.  As over one subgroup
  this is not derivable from the fields above, so it is asked of the cone-off,
  which is where Hull proves it. -/
  injOn_of_dist : ∀ {Q : Type u} [Group Q] (q : G →* Q),
    q.ker = Subgroup.normalClosure (⋃ lam : Λ, (K lam : Set G)) →
      ∀ g : G, g ≠ 1 → dist base (g • base) < sep → q g ≠ 1
  /-- The conjugates of each `K lam` rotate very much about the corresponding
  apices, in the sense of DGO Definition 2.12(c). -/
  veryRotating : ∀ (lam : Λ) (g k : G), k ∈ K lam → g * k * g⁻¹ ≠ 1 →
    ∀ x y : Space, 20 * delta ≤ dist x (g • apex lam) →
      dist x (g • apex lam) ≤ 40 * delta →
        20 * delta ≤ dist y (g • apex lam) →
          dist y (g • apex lam) ≤ 40 * delta →
            dist ((g * k * g⁻¹) • x) y ≤ 15 * delta →
              ∀ f : ℝ → Space, IsGeodesicSegment f 0 (dist x y) → f 0 = x →
                f (dist x y) = y →
                  ∃ s ∈ Set.Icc (0 : ℝ) (dist x y), f s = g • apex lam

namespace ConeOffData₂

instance instMetric {G : Type u} [Group G] {Λ : Type w} {A : Alphabet G}
    {K : Λ → Subgroup G} {L : ℝ} (P : ConeOffData₂ A K L) :
    PseudoMetricSpace P.Space := P.metric

instance instAction {G : Type u} [Group G] {Λ : Type w} {A : Alphabet G}
    {K : Λ → Subgroup G} {L : ℝ} (P : ConeOffData₂ A K L) :
    MulAction G P.Space := P.action

/-- **The apices of the family**: the union of the orbits of the individual
apices. -/
def apexSet {G : Type u} [Group G] {Λ : Type w} {A : Alphabet G}
    {K : Λ → Subgroup G} {L : ℝ} (P : ConeOffData₂ A K L) : Set P.Space :=
  {x | ∃ (lam : Λ) (g : G), g • P.apex lam = x}

theorem mem_apexSet {G : Type u} [Group G] {Λ : Type w} {A : Alphabet G}
    {K : Λ → Subgroup G} {L : ℝ} (P : ConeOffData₂ A K L) {x : P.Space} :
    x ∈ P.apexSet ↔ ∃ (lam : Λ) (g : G), g • P.apex lam = x := Iff.rfl

theorem apex_mem_apexSet {G : Type u} [Group G] {Λ : Type w} {A : Alphabet G}
    {K : Λ → Subgroup G} {L : ℝ} (P : ConeOffData₂ A K L) (lam : Λ) :
    P.apex lam ∈ P.apexSet :=
  ⟨lam, 1, one_smul G (P.apex lam)⟩

end ConeOffData₂

end HullSC
end GroupApproximation
