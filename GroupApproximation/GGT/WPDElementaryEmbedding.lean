import GroupApproximation.GGT.ElementaryClosure
import GroupApproximation.GGT.HullSCConeOff
import GroupApproximation.GGT.WPDAcylindricalHyperbolicity

/-!
# Dahmani--Guirardel--Osin's Theorem 6.8: the plan, and the reduction

`GGT.DGOTheorem68` is the implication `(AH₃) ⇒ (AH₄)` of Osin's Theorem 1.2:

> a loxodromic WPD element lies in a proper hyperbolically embedded subgroup.

This module fixes the shape of the proof, proves the parts that are not
geometry, and leaves **one** named geometric proposition.  It does not prove
Theorem 6.8.

## The four obligations

Take `E := Elementary.elementaryClosure D.elt` --- Osin's `E(g)`, the elements
conjugating a nonzero power of `g` to a nonzero power of `g`.  Then
`DGOTheorem68` asks for

* (i)   `D.elt ∈ E` --- `Elementary.self_mem_elementaryClosure`, proved;
* (ii)  `E ≠ ⊤`;
* (iii) `Γ(G, X ⊔ E)` hyperbolic, for a base `X` of one's choice;
* (iv)  every relative ball `d̂_E(1, ·) ≤ n` finite,

where (iii) and (iv) are the two fields of
`GGT.RelGenSet.IsHyperbolicallyEmbedded` for `HullSC.coneOff X E`, and
`HullSC.isHypEmbeddedOf_coneOff` turns them into `IsHypEmbedded G E`.
`dgoTheorem68_of` is that assembly: it takes (ii) and (iii)+(iv) as the two
named propositions `ElementaryClosureProper` and
`ElementaryConeOffHypEmbedded` and proves `DGOTheorem68`.

**(iii) and (iv) are coupled through `X` and cannot be split between two
lanes.**  Enlarging `X` helps (iii) and hurts (iv): `HullSC.coneOff` is one
relative generating set, and both fields speak about it.  So the named
proposition below existentially quantifies `X` and carries both fields.

## The plan for the geometry

**Step 1, proved here: the space may be taken to be `G`.**
`exists_ah3Data_orbit` replaces the `(AH₃)` datum by one whose space is `G`
carrying the *orbit pseudo-metric* `d(a,b) = d(a·x₀, b·x₀)`, with `G` acting by
left translation.  Nothing is lost, because every clause of `AH3Data` is a
statement about distances *between points of the orbit*: the four-point
condition, loxodromy of `g` at `x₀`, and the `ε`-stabilisers the WPD condition
counts are literally the same numbers and the same sets.  This is available
because hyperbolicity here is Gromov's four-point condition, which a subspace
inherits; Dahmani--Guirardel--Osin work with geodesic spaces, where passing to
an orbit requires thickening it first.

After Step 1 the datum is: a left-invariant pseudo-metric `d` on `G`, an element
`g` with `l·n - B ≤ d(1, gⁿ)`, and the WPD condition in the form

> for every `ε` there is `M` with `{k | d(1,k) ≤ ε ∧ d(g^M, k·g^M) ≤ ε}` finite,

which is a properness statement about `d` along the quasi-axis `n ↦ gⁿ`, and the
action is transitive, so the coboundedness that Dahmani--Guirardel--Osin's §4
assumes is free.

**Step 2, the base.**  `X := displacementBall x₀ C = {a | d(1, a) ≤ C}`.  It is
symmetric (`displacementBall_inv_mem`), and it generates as soon as it contains
one generating set (`displacementBall_isSymmetricGeneratingSet`), which for a
finitely generated `G` holds for every `C` past the largest displacement of a
finite generating set.  The manuscript's `E` is finitely presented, so that is
the case that matters; for a `G` that is not finitely generated the base has to
be enlarged by a generating set, and the enlargement is exactly what Osin's
Theorem 5.4 has to repair on the other side.

**Step 3, the two fields.**  This is Dahmani--Guirardel--Osin §4 and is what
remains.  (iii) says the coned-off graph is hyperbolic; (iv) says a word of
bounded relative length avoiding the `E`-edges spells only finitely many
elements of `E`, and the mechanism is that such a word traces a path in `G`
which leaves and re-enters the quasi-axis, so that the element it spells moves
two far apart points of the axis a bounded amount --- at which point the WPD
condition of Step 1 bounds the number of possibilities.

## Two traps, both already refuted in the repository

* `GGT.not_isHypEmbeddedOf_of_subset`: an infinite `E` inside the base is never
  hyperbolically embedded over it.  `E` is infinite here
  (`infinite_elementaryClosure`), so the cheap route --- take `X = G`, where
  `Γ(G, X ⊔ E)` has diameter one and is hyperbolic by
  `isHyperbolicSpace_of_bounded` --- is closed, and `not_isHypEmbeddedOf_univ`
  records that.  The base must be thin enough that `E` is not shortcuttable.
* `GGT.RelGenSet.not_isLoxodromic_of_mem_fam`: no element of `E` is loxodromic
  on `Γ(G, X ⊔ E)`.  So every use of loxodromy of `g` is a statement about the
  space of Step 1, never about the cone-off.

## A note on (ii), for whoever discharges it

`E ≠ ⊤` does **not** follow from `¬ IsVirtuallyCyclic G` by way of
`GGT.actsNonElementarily_of_no_common_power`: that route needs a pair of
elements with no common nonzero power, and a group can be non-virtually-cyclic
without having one.  A Tarski monster of exponent `p` is infinite, torsion --- so
not virtually cyclic --- and any two of its elements satisfy `a^p = b^p = 1`.
The `(AH₃)` datum has to be used, not just the non-virtual-cyclicity: what rules
the monster out is that it has no element of infinite order, hence no loxodromic
one.
-/

namespace GroupApproximation
namespace GGT

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u v

/-! ## Bounded spaces are hyperbolic -/

/-- **A space of diameter at most `C` is `C`-hyperbolic.**  Every Gromov product
is at most `C` and every Gromov product is nonnegative, so the four-point
condition holds with nothing to check.

This is what makes the degenerate base `X = G` hyperbolic, and it is the reason
the base cannot be chosen that way: the local finiteness clause then fails, by
`not_isHypEmbeddedOf_univ`. -/
theorem isHyperbolicSpace_of_bounded {X : Type v} [PseudoMetricSpace X] {C : ℝ}
    (hC : ∀ p q : X, dist p q ≤ C) : IsHyperbolicSpace C X := by
  intro w x y z
  have hxy : gromovProduct x y w ≤ C := by
    have h1 := hC x w
    have h2 := hC y w
    have h3 : (0 : ℝ) ≤ dist x y := dist_nonneg
    unfold gromovProduct
    linarith
  have hnn := gromovProduct_nonneg x z w
  have hmin : min (gromovProduct x y w) (gromovProduct y z w) ≤ C :=
    le_trans (min_le_left _ _) hxy
  linarith

/-- **The base cannot be everything.**  An infinite subgroup is not
hyperbolically embedded over a base containing it, and `Set.univ` contains it.
So the fact that coning off everything makes the relative Cayley graph bounded,
hence hyperbolic, is of no use. -/
theorem not_isHypEmbeddedOf_univ {G : Type u} [Group G] {H : Subgroup G}
    (hinf : (H : Set G).Infinite) :
    ¬ IsHypEmbeddedOf G (Set.univ : Set G) H :=
  not_isHypEmbeddedOf_of_subset (Set.subset_univ _) hinf

/-! ## The orbit pseudo-metric: the space may be taken to be `G` -/

section Orbit

/-- **`G` with the orbit pseudo-metric of a basepoint**: `d(a,b) = d(a·x₀, b·x₀)`.
A type synonym for `G`, indexed by the basepoint. -/
def OrbitSpace {G : Type u} [Group G] {X : Type v} (_x₀ : X) : Type u := G

/-- The point of `OrbitSpace x₀` named by a group element. -/
def OrbitSpace.of {G : Type u} [Group G] {X : Type v} (x₀ : X) (a : G) :
    OrbitSpace (G := G) x₀ := a

/-- The group element naming a point of `OrbitSpace x₀`. -/
def OrbitSpace.val {G : Type u} [Group G] {X : Type v} {x₀ : X}
    (p : OrbitSpace (G := G) x₀) : G := p

@[simp] theorem OrbitSpace.val_of {G : Type u} [Group G] {X : Type v} (x₀ : X)
    (a : G) : OrbitSpace.val (OrbitSpace.of (G := G) x₀ a) = a := rfl

/-- The orbit pseudo-metric.  Symmetry and the triangle inequality are those of
the ambient space at the orbit points. -/
noncomputable instance instPseudoMetricSpaceOrbitSpace {G : Type u} [Group G]
    {X : Type v} [PseudoMetricSpace X] [MulAction G X] (x₀ : X) :
    PseudoMetricSpace (OrbitSpace (G := G) x₀) where
  dist p q := dist ((OrbitSpace.val p) • x₀) ((OrbitSpace.val q) • x₀)
  dist_self p := dist_self _
  dist_comm p q := dist_comm _ _
  dist_triangle p q r := dist_triangle _ _ _

/-- `G` acts on `OrbitSpace x₀` by left translation. -/
instance instMulActionOrbitSpace {G : Type u} [Group G] {X : Type v} (x₀ : X) :
    MulAction G (OrbitSpace (G := G) x₀) :=
  inferInstanceAs (MulAction G G)

@[simp] theorem OrbitSpace.dist_eq {G : Type u} [Group G] {X : Type v}
    [PseudoMetricSpace X] [MulAction G X] {x₀ : X}
    (p q : OrbitSpace (G := G) x₀) :
    dist p q = dist ((OrbitSpace.val p) • x₀) ((OrbitSpace.val q) • x₀) := rfl

@[simp] theorem OrbitSpace.val_smul {G : Type u} [Group G] {X : Type v}
    {x₀ : X} (g : G) (p : OrbitSpace (G := G) x₀) :
    OrbitSpace.val (g • p) = g * OrbitSpace.val p := rfl

/-- **Left translation on the orbit pseudo-metric is by isometries.** -/
theorem isIsometricAction_orbitSpace {G : Type u} [Group G] {X : Type v}
    [PseudoMetricSpace X] [MulAction G X] (hiso : IsIsometricAction G X) (x₀ : X) :
    IsIsometricAction G (OrbitSpace (G := G) x₀) := by
  intro g p q
  show dist ((g * OrbitSpace.val p) • x₀) ((g * OrbitSpace.val q) • x₀)
    = dist ((OrbitSpace.val p) • x₀) ((OrbitSpace.val q) • x₀)
  rw [mul_smul, mul_smul]
  exact hiso g _ _

/-- **The orbit pseudo-metric is hyperbolic with the same constant.**  Its
Gromov products *are* the Gromov products of the orbit points. -/
theorem isHyperbolicSpace_orbitSpace {G : Type u} [Group G] {X : Type v}
    [PseudoMetricSpace X] [MulAction G X] {δ : ℝ} (hδ : IsHyperbolicSpace δ X)
    (x₀ : X) : IsHyperbolicSpace δ (OrbitSpace (G := G) x₀) := by
  intro w p q r
  exact hδ ((OrbitSpace.val w) • x₀) ((OrbitSpace.val p) • x₀)
    ((OrbitSpace.val q) • x₀) ((OrbitSpace.val r) • x₀)

/-- **Loxodromy transfers to the orbit**, at the basepoint `1`. -/
theorem isLoxodromic_orbitSpace {G : Type u} [Group G] {X : Type v}
    [PseudoMetricSpace X] [MulAction G X] {g : G} {x₀ : X}
    (h : IsLoxodromic g x₀) :
    IsLoxodromic g (OrbitSpace.of (G := G) x₀ 1) := by
  obtain ⟨l, hl, B, hB, hle⟩ := h
  refine ⟨l, hl, B, hB, fun n => ?_⟩
  have hd : dist (OrbitSpace.of (G := G) x₀ 1)
      ((g ^ n) • OrbitSpace.of (G := G) x₀ 1) = dist x₀ ((g ^ n) • x₀) := by
    show dist (((1 : G)) • x₀) (((g ^ n) * (1 : G)) • x₀) = dist x₀ ((g ^ n) • x₀)
    rw [one_smul, mul_one]
  rw [hd]
  exact hle n

/-- **The WPD condition transfers to the orbit**: the `ε`-stabilisers it counts
are the same sets. -/
theorem isWPDAt_orbitSpace {G : Type u} [Group G] {X : Type v}
    [PseudoMetricSpace X] [MulAction G X] {g : G} {x₀ : X} (h : IsWPDAt g x₀) :
    IsWPDAt g (OrbitSpace.of (G := G) x₀ 1) := by
  intro ε hε
  obtain ⟨M, hM⟩ := h ε hε
  refine ⟨M, hM.subset ?_⟩
  intro k hk
  rw [mem_pairStab] at hk
  obtain ⟨h1, h2⟩ := hk
  rw [mem_pairStab]
  refine ⟨?_, ?_⟩
  · have e : dist (OrbitSpace.of (G := G) x₀ 1)
        (k • OrbitSpace.of (G := G) x₀ 1) = dist x₀ (k • x₀) := by
      show dist (((1 : G)) • x₀) ((k * (1 : G)) • x₀) = dist x₀ (k • x₀)
      rw [one_smul, mul_one]
    rw [← e]
    exact h1
  · have e : dist ((g ^ M) • OrbitSpace.of (G := G) x₀ 1)
        (k • ((g ^ M) • OrbitSpace.of (G := G) x₀ 1))
      = dist ((g ^ M) • x₀) (k • ((g ^ M) • x₀)) := by
      show dist (((g ^ M) * (1 : G)) • x₀) ((k * ((g ^ M) * (1 : G))) • x₀)
        = dist ((g ^ M) • x₀) (k • ((g ^ M) • x₀))
      rw [mul_one, mul_smul]
    rw [← e]
    exact h2

end Orbit

/-- **The `(AH₃)` datum may be taken on `G` itself.**  Given any `(AH₃)` datum,
there is one with the same distinguished element whose space is `G` with the
orbit pseudo-metric.  The action is then left translation, hence transitive, so
coboundedness is free. -/
theorem exists_ah3Data_orbit {G : Type u} [Group G] (D : AH3Data.{u, v} G) :
    ∃ D' : AH3Data.{u, u} G, D'.elt = D.elt := by
  letI := D.metricSpace
  letI := D.mulAction
  exact ⟨AH3Data.ofData (OrbitSpace (G := G) D.base)
    (isIsometricAction_orbitSpace D.isometric D.base) D.delta
    (isHyperbolicSpace_orbitSpace D.hyperbolic D.base) D.elt
    (OrbitSpace.of (G := G) D.base 1) (isLoxodromic_orbitSpace D.loxodromic)
    (isWPDAt_orbitSpace D.wpd), rfl⟩

/-! ## The displacement ball, the base of the cone-off -/

section Ball

/-- **The `C`-displacement ball** `{a | d(x₀, a·x₀) ≤ C}`, the base to cone off
`E(g)` over. -/
def displacementBall {G : Type u} [Group G] {X : Type v} [PseudoMetricSpace X]
    [MulAction G X] (x₀ : X) (C : ℝ) : Set G := {a : G | dist x₀ (a • x₀) ≤ C}

theorem mem_displacementBall {G : Type u} [Group G] {X : Type v}
    [PseudoMetricSpace X] [MulAction G X] {x₀ : X} {C : ℝ} {a : G} :
    a ∈ displacementBall (G := G) x₀ C ↔ dist x₀ (a • x₀) ≤ C := Iff.rfl

/-- **The displacement ball is symmetric.**  Moving the basepoint by `a⁻¹` costs
what moving it by `a` costs, because the action is isometric. -/
theorem displacementBall_inv_mem {G : Type u} [Group G] {X : Type v}
    [PseudoMetricSpace X] [MulAction G X] (hiso : IsIsometricAction G X) (x₀ : X)
    (C : ℝ) {a : G} (ha : a ∈ displacementBall (G := G) x₀ C) :
    a⁻¹ ∈ displacementBall (G := G) x₀ C := by
  have h : dist (a • x₀) (a • (a⁻¹ • x₀)) = dist x₀ (a⁻¹ • x₀) :=
    hiso a x₀ (a⁻¹ • x₀)
  rw [smul_inv_smul] at h
  show dist x₀ (a⁻¹ • x₀) ≤ C
  rw [← h, dist_comm]
  exact ha

/-- **The displacement ball is an alphabet as soon as it contains a generating
set.**  For a finitely generated `G` this holds for every `C` past the largest
displacement of a finite generating set, so the base of the cone-off is a
genuine `Alphabet G`. -/
theorem displacementBall_isSymmetricGeneratingSet {G : Type u} [Group G]
    {X : Type v} [PseudoMetricSpace X] [MulAction G X]
    (hiso : IsIsometricAction G X)
    (x₀ : X) (C : ℝ) {Y : Set G} (hY : Subgroup.closure Y = ⊤)
    (hYC : Y ⊆ displacementBall (G := G) x₀ C) :
    IsSymmetricGeneratingSet (displacementBall (G := G) x₀ C) := by
  refine ⟨fun a ha => displacementBall_inv_mem hiso x₀ C ha, ?_⟩
  refine eq_top_iff.mpr ?_
  rw [← hY]
  exact Subgroup.closure_mono hYC

end Ball

/-! ## The elementary closure is infinite -/

/-- **`E(g)` is infinite when `g` is loxodromic.**  It contains `g`, whose order
is infinite.  This is what makes the trap of `not_isHypEmbeddedOf_univ` fire,
and it is the infinitude clause `(AH₄)` asks for. -/
theorem infinite_elementaryClosure {G : Type u} [Group G] {X : Type v}
    [PseudoMetricSpace X] [MulAction G X] {g : G} {x : X}
    (hlox : IsLoxodromic g x) :
    ((Elementary.elementaryClosure g : Subgroup G) : Set G).Infinite :=
  infinite_of_mem_of_isLoxodromic hlox (Elementary.self_mem_elementaryClosure g)

/-! ## The two named obligations, and the assembly -/

/-- **The geometry of Dahmani--Guirardel--Osin's Theorem 6.8**: over a suitable
base the elementary closure of a loxodromic WPD element is hyperbolically
embedded.

Both fields of `IsHyperbolicallyEmbedded` are here, and deliberately so: they
are statements about one and the same relative generating set, and enlarging the
base helps the first and hurts the second.  The datum is taken on `G` itself,
which `exists_ah3Data_orbit` shows is no loss. -/
def ElementaryConeOffHypEmbedded : Prop :=
  ∀ (G : Type u) [Group G] (D : AH3Data.{u, u} G), ¬ IsVirtuallyCyclic G →
    ∃ X : Alphabet G,
      (HullSC.coneOff X (Elementary.elementaryClosure D.elt)).IsHyperbolicallyEmbedded

/-- **The elementary closure of a loxodromic WPD element is a proper subgroup.**
Dahmani--Guirardel--Osin prove it by way of `E(g)` being virtually cyclic, which
`¬ IsVirtuallyCyclic G` then contradicts; the repository's partial machinery for
it is `Elementary.exists_notMem_elementaryClosure_of_centralizer`.  It is not a
formal consequence of `¬ IsVirtuallyCyclic G` alone --- see the note in the
module docstring. -/
def ElementaryClosureProper : Prop :=
  ∀ (G : Type u) [Group G] (D : AH3Data.{u, u} G), ¬ IsVirtuallyCyclic G →
    Elementary.elementaryClosure D.elt ≠ ⊤

/-- **Theorem 6.8 from the two obligations.**  The subgroup is the elementary
closure; membership is `self_mem_elementaryClosure`; properness is the second
obligation; and the hyperbolic embedding is the cone-off of the first, through
`HullSC.isHypEmbeddedOf_coneOff`.  The passage from an arbitrary space to `G`
itself is `exists_ah3Data_orbit`, which is why both obligations may be stated
for a datum on `G`. -/
theorem dgoTheorem68_of (hcone : ElementaryConeOffHypEmbedded.{u})
    (hproper : ElementaryClosureProper.{u}) : DGOTheorem68.{u, v} := by
  intro G _ D hvc
  obtain ⟨D', hD'⟩ := exists_ah3Data_orbit D
  obtain ⟨X, hX⟩ := hcone G D' hvc
  have hne := hproper G D' hvc
  rw [hD'] at hX hne
  exact ⟨Elementary.elementaryClosure D.elt,
    Elementary.self_mem_elementaryClosure D.elt, hne,
    (HullSC.isHypEmbeddedOf_coneOff X (Elementary.elementaryClosure D.elt)
      hX).isHypEmbedded⟩

end GGT
end GroupApproximation
