import GroupApproximation.Sofic.HullSuitableDefectSubgroup

/-!
# Hull's Definition 1.4 in full, and what its geometric clause forces

`Sofic.HullSuitableDefectSubgroup` builds the algebraic half of Hull's suitable
subgroup and says the geometric clause is "not stateable in this library".  That
was true of `Sofic.TorsionFreeFullMFRadical`'s vocabulary and it is not true of
Lean: acylindricity, hyperbolicity and non-elementarity are ordinary
∀∃-statements about a metric space and an action, and Mathlib has metric spaces.
This module writes them down.

Nothing here is an opaque predicate.  Every notion below is a definition with a
body, so a reader can check that it says what Hull's Definition 1.4 says, and
the theorems that follow are theorems about that body rather than about a name.

## The definitions

* `gromovProduct` and `IsHyperbolicSpace δ X` --- Gromov's four-point condition.
* `IsAcylindrical` --- Osin's condition: for every `ε` there are `R` and `N` such
  that any two points at distance at least `R` are moved by at most `ε` by at
  most `N` group elements.
* `IsLoxodromic g x` --- the orbit of `x` under the powers of `g` escapes every
  bounded set.
* `Independent g h x` --- the Gromov products of the two power-orbits stay
  bounded: the two axes have disjoint endpoints.
* `ActsNonElementarily S x` --- `S` contains two independent loxodromics.  This
  is the working form of non-elementarity for acylindrical actions.
* `IsSuitable` --- Hull's Definition 1.4, all three clauses, with the third one
  spelled as in `Sofic.HullSuitableDefectSubgroup`.

## What is proved

The point of writing the clause down is that the relation between it and the
unconditional object becomes a theorem instead of a claim:

> `IsSuitable.toIsAlgebraicallySuitable` --- **a suitable subgroup is
> algebraically suitable.**

So `IsAlgebraicallySuitable` is not an approximation of Hull's definition chosen
for convenience: it is exactly the part of it that survives forgetting the
space, and the object built unconditionally in `Sofic.ExplicitSuitableDefect`
carries everything Hull's hypothesis carries except the geometry itself.  The
proof runs through three facts that are worth having on their own:

* `not_isOfFinOrder_of_isLoxodromic` --- a loxodromic element has infinite
  order.  Its powers would otherwise return to the basepoint infinitely often.
* `notMem_zpowers_of_independent` --- an element independent from `g` is not a
  power of `g`.  If it were, the two orbits would meet at every scale and their
  Gromov products would be unbounded.
* `not_actsNonElementarily_of_bounded` --- **the clause cannot be cheated.**  On
  a bounded space every action is acylindrical and every space is hyperbolic, so
  clauses (1) and (3) alone are satisfiable by a trivial choice; clause (2) is
  what forbids it, and it fails outright when the orbit is bounded.

## What is not proved, and why

That some ambient group admits an action making the compression defect
non-elementary.  With the definitions here that is a single Lean proposition ---
`∃ X δ x, IsSuitable δ N x` for the defect `N` --- and it is the geometric half
of the manuscript's Question 2.  It is open mathematics about the group, not a
missing definition: `notes/HULL_ROUTING_AUDIT_2026-08-16.md` §3.1 shows the
ascending HNN skeleton's Bass--Serre action is quasi-parabolic and therefore not
acylindrical, and whether the skeleton lies in `𝒜ℋ` for some other action is
settled by no source in either direction.  This module makes that the only thing
left, and makes it a statement rather than a paragraph.
-/

namespace GroupApproximation
namespace HullGeometry

universe u v

variable {G : Type u} [Group G] {X : Type v} [PseudoMetricSpace X] [MulAction G X]

/-! ## The action -/

/-- The action is by isometries.  Carried as a hypothesis rather than a
typeclass so that the definitions below say exactly what they need. -/
def IsIsometricAction (G : Type u) (X : Type v) [Group G] [PseudoMetricSpace X]
    [MulAction G X] : Prop :=
  ∀ (g : G) (x y : X), dist (g • x) (g • y) = dist x y

/-! ## Hyperbolicity -/

/-- The Gromov product of `x` and `y` based at `w`. -/
def gromovProduct (x y w : X) : ℝ := (dist x w + dist y w - dist x y) / 2

@[simp] theorem gromovProduct_self (y w : X) :
    gromovProduct y y w = dist y w := by
  unfold gromovProduct
  rw [dist_self]
  ring

/-- Gromov's four-point condition. -/
def IsHyperbolicSpace (δ : ℝ) (X : Type v) [PseudoMetricSpace X] : Prop :=
  ∀ w x y z : X,
    min (gromovProduct x y w) (gromovProduct y z w) - δ ≤ gromovProduct x z w

/-! ## Acylindricity -/

/-- Osin's acylindricity condition for a group action on a metric space. -/
def IsAcylindrical (G : Type u) (X : Type v) [Group G] [PseudoMetricSpace X]
    [MulAction G X] : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ (R : ℝ) (N : ℕ), ∀ x y : X, R ≤ dist x y →
    {g : G | dist x (g • x) ≤ ε ∧ dist y (g • y) ≤ ε}.Finite ∧
      {g : G | dist x (g • x) ≤ ε ∧ dist y (g • y) ≤ ε}.ncard ≤ N

/-! ## Loxodromics, independence, non-elementarity -/

/-- `g` is loxodromic at `x` when its power orbit escapes every bounded set. -/
def IsLoxodromic (g : G) (x : X) : Prop :=
  Filter.Tendsto (fun n : ℕ => dist x ((g ^ n) • x)) Filter.atTop Filter.atTop

/-- `g` and `h` are independent at `x` when the Gromov products of their power
orbits stay bounded: their axes do not share an endpoint.  Powers range over
`ℤ`, which is what makes `g` and `g⁻¹` correctly dependent. -/
def Independent (g h : G) (x : X) : Prop :=
  ∃ C : ℝ, ∀ n m : ℤ, gromovProduct ((g ^ n) • x) ((h ^ m) • x) x ≤ C

/-- `S` acts non-elementarily at `x` when it contains two independent
loxodromics. -/
def ActsNonElementarily (S : Subgroup G) (x : X) : Prop :=
  ∃ g ∈ S, ∃ h ∈ S, IsLoxodromic g x ∧ IsLoxodromic h x ∧ Independent g h x

/-! ## Hull's Definition 1.4 -/

/-- **Hull's Definition 1.4.**  `S` is suitable for the action of `G` on `X`
based at `x` with hyperbolicity constant `δ`.

Clause (1) is `hyperbolic` together with `acylindrical` and `isometric`; clause
(2) is `nonElementary`; clause (3) is `normalizesNoNontrivialFinite`, spelled
exactly as in `Sofic.HullSuitableDefectSubgroup`. -/
structure IsSuitable (δ : ℝ) (S : Subgroup G) (x : X) : Prop where
  /-- The action is by isometries. -/
  isometric : IsIsometricAction G X
  /-- Clause (1), first half: the space is hyperbolic. -/
  hyperbolic : IsHyperbolicSpace δ X
  /-- Clause (1), second half: the action is acylindrical. -/
  acylindrical : IsAcylindrical G X
  /-- Clause (2): the induced action of `S` is non-elementary. -/
  nonElementary : ActsNonElementarily S x
  /-- Clause (3): `S` normalizes no nontrivial finite subgroup. -/
  normalizesNoNontrivialFinite : HullSuitable.NormalizesNoNontrivialFinite S

/-! ## A loxodromic element has infinite order -/

/-- A loxodromic element has infinite order: a finite order would send its
power orbit back to the basepoint arbitrarily late, and a sequence tending to
infinity cannot return to `0`. -/
theorem not_isOfFinOrder_of_isLoxodromic {g : G} {x : X}
    (hg : IsLoxodromic g x) : ¬ IsOfFinOrder g := by
  intro hfin
  obtain ⟨k, hk, hgk⟩ := isOfFinOrder_iff_pow_eq_one.mp hfin
  have hev := hg.eventually_ge_atTop (1 : ℝ)
  rw [Filter.eventually_atTop] at hev
  obtain ⟨M, hM⟩ := hev
  have hle : M ≤ k * M := Nat.le_mul_of_pos_left M hk
  have h1 := hM (k * M) hle
  rw [pow_mul, hgk, one_pow, one_smul, dist_self] at h1
  linarith

/-! ## Independence detects that one element is not a power of the other -/

/-- Reversing a power does not change how far it moves the basepoint. -/
theorem dist_zpow_neg {g : G} {x : X} (hiso : IsIsometricAction G X) (n : ℤ) :
    dist x ((g ^ (-n)) • x) = dist x ((g ^ n) • x) := by
  have h := hiso (g ^ n) x ((g ^ (-n)) • x)
  rw [← mul_smul, ← zpow_add, add_neg_cancel, zpow_zero, one_smul] at h
  rw [← h, dist_comm]

/-- An element independent from `g` is not a power of `g`.  If `h = g ^ j` then
the pair `(j * m, m)` puts the two orbits at the same point, where the Gromov
product is the distance from the basepoint, and `h` loxodromic makes that
unbounded. -/
theorem notMem_zpowers_of_independent {g h : G} {x : X}
    (hh : IsLoxodromic h x) (hind : Independent g h x) :
    h ∉ Subgroup.zpowers g := by
  rintro ⟨j, rfl⟩
  obtain ⟨C, hC⟩ := hind
  have hev := hh.eventually_ge_atTop (C + 1)
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  have hkey := hC (j * (N : ℤ)) (N : ℤ)
  rw [zpow_mul] at hkey
  rw [gromovProduct_self] at hkey
  rw [zpow_natCast] at hkey
  have h1 := hN N le_rfl
  rw [dist_comm] at hkey
  linarith

/-! ## Non-elementarity delivers the algebraic clauses -/

/-- A non-elementary subgroup contains an infinite-order element generating a
proper subgroup: the first of the two independent loxodromics, made proper by
the second. -/
theorem exists_proper_infiniteOrder_of_actsNonElementarily {S : Subgroup G}
    {x : X} (hne : ActsNonElementarily S x) :
    ∃ k ∈ S, ¬ IsOfFinOrder k ∧ Subgroup.zpowers k < S := by
  obtain ⟨g, hgS, h, hhS, hg, hh, hind⟩ := hne
  refine ⟨g, hgS, not_isOfFinOrder_of_isLoxodromic hg, ?_⟩
  refine lt_of_le_of_ne (Subgroup.zpowers_le.mpr hgS) ?_
  intro hEq
  refine notMem_zpowers_of_independent hh hind ?_
  rw [hEq]
  exact hhS

/-- A non-elementary subgroup is infinite. -/
theorem infinite_of_actsNonElementarily {S : Subgroup G} {x : X}
    (hne : ActsNonElementarily S x) : Infinite S := by
  obtain ⟨k, hkS, hk, -⟩ := exists_proper_infiniteOrder_of_actsNonElementarily hne
  exact HullSuitable.infinite_of_mem_of_not_isOfFinOrder hkS hk

/-! ## The comparison theorem -/

/-- **A suitable subgroup is algebraically suitable.**

This is the theorem that makes `HullSuitable.IsAlgebraicallySuitable` the right
object: it is not a convenient weakening of Hull's Definition 1.4 but exactly
what that definition says once the space is forgotten.  Clause (3) transfers
verbatim; the hypotheses of Hull's Lemma 5.8 that are not geometric come from
clause (2). -/
theorem IsSuitable.toIsAlgebraicallySuitable {δ : ℝ} {S : Subgroup G} {x : X}
    (hs : IsSuitable δ S x) : HullSuitable.IsAlgebraicallySuitable S :=
  ⟨hs.normalizesNoNontrivialFinite,
    exists_proper_infiniteOrder_of_actsNonElementarily hs.nonElementary⟩

/-- A suitable subgroup is infinite. -/
theorem IsSuitable.infinite {δ : ℝ} {S : Subgroup G} {x : X}
    (hs : IsSuitable δ S x) : Infinite S :=
  infinite_of_actsNonElementarily hs.nonElementary

/-- A suitable subgroup is nontrivial. -/
theorem IsSuitable.ne_bot {δ : ℝ} {S : Subgroup G} {x : X}
    (hs : IsSuitable δ S x) : S ≠ ⊥ :=
  hs.toIsAlgebraicallySuitable.ne_bot

/-! ## The clause cannot be cheated -/

/-- **Clause (2) is the whole content.**  On a bounded orbit no subgroup acts
non-elementarily, so the temptation to satisfy Hull's definition by taking a
bounded space --- where every action is acylindrical and every space is
hyperbolic --- is closed off.  In particular the definition is not vacuously
satisfiable. -/
theorem not_actsNonElementarily_of_bounded {x : X} {S : Subgroup G}
    (hbdd : ∃ C : ℝ, ∀ g : G, dist x (g • x) ≤ C) :
    ¬ ActsNonElementarily S x := by
  rintro ⟨g, -, -, -, hg, -, -⟩
  obtain ⟨C, hC⟩ := hbdd
  have hev := hg.eventually_ge_atTop (C + 1)
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  have h1 := hN N le_rfl
  have h2 := hC (g ^ N)
  linarith

/-- The same statement for a suitable subgroup: suitability forces an unbounded
orbit. -/
theorem IsSuitable.not_bounded {δ : ℝ} {S : Subgroup G} {x : X}
    (hs : IsSuitable δ S x) : ¬ ∃ C : ℝ, ∀ g : G, dist x (g • x) ≤ C :=
  fun hbdd => not_actsNonElementarily_of_bounded hbdd hs.nonElementary

/-! ## What a suitable geometry forbids

Suitability is not only a constraint on the subgroup; it is a constraint on
what can commute with it.  The theorem below is the elementary half of the fact
that a loxodromic element of an acylindrical action has a virtually cyclic
centralizer, and it is proved here from the definitions above with nothing
imported. -/

/-- Two independent loxodromics separate: their orbits eventually lie
arbitrarily far apart.  This is the Gromov-product bound of `Independent` read
as a lower bound on distance. -/
theorem exists_far_apart {g h : G} {x : X} (hg : IsLoxodromic g x)
    (hind : Independent g h x) (R : ℝ) :
    ∃ n : ℕ, R ≤ dist ((g ^ n) • x) ((h ^ n) • x) := by
  obtain ⟨C, hC⟩ := hind
  have hev := hg.eventually_ge_atTop (R + 2 * C)
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  refine ⟨N, ?_⟩
  have h1 := hC (N : ℤ) (N : ℤ)
  rw [zpow_natCast, zpow_natCast] at h1
  simp only [gromovProduct] at h1
  have h2 := hN N le_rfl
  have h3 : (0:ℝ) ≤ dist ((h ^ N) • x) x := dist_nonneg
  have h4 : dist ((g ^ N) • x) x = dist x ((g ^ N) • x) := dist_comm _ _
  linarith

/-- **An element with bounded orbit commuting with two independent loxodromics
has finite order.**

This is the constraint a suitable geometry places on the ambient group, and it
is proved from the definitions: `c` commutes with `g` and `h`, so it moves every
point of both orbits by exactly `dist x (c • x)`; acylindricity applied to two
points of those orbits that are far apart then confines all the powers of `c`
to one finite set, and an infinite-order element has infinitely many powers. -/
theorem isOfFinOrder_of_commutes_of_bounded
    (hiso : IsIsometricAction G X) (hacy : IsAcylindrical G X)
    {g h c : G} {x : X} (hg : IsLoxodromic g x) (hh : IsLoxodromic h x)
    (hind : Independent g h x) (hcg : Commute c g) (hch : Commute c h)
    {B : ℝ} (hbdd : ∀ j : ℤ, dist x ((c ^ j) • x) ≤ B) :
    IsOfFinOrder c := by
  by_contra hfin
  have hB : (0:ℝ) ≤ B := by
    have h0 := hbdd 0
    rw [zpow_zero, one_smul, dist_self] at h0
    exact h0
  obtain ⟨R, N₀, hRN⟩ := hacy (B + 1) (by linarith)
  obtain ⟨n, hn⟩ := exists_far_apart hg hind R
  obtain ⟨hfinite, -⟩ := hRN ((g ^ n) • x) ((h ^ n) • x) hn
  have hmove : ∀ (k : G) (j : ℤ), Commute c k →
      dist ((k ^ n) • x) ((c ^ j) • ((k ^ n) • x)) ≤ B := by
    intro k j hck
    have hcomm : (c ^ j) * (k ^ n) = (k ^ n) * (c ^ j) :=
      ((hck.zpow_left j).pow_right n).eq
    have hstep : (c ^ j) • ((k ^ n) • x) = (k ^ n) • ((c ^ j) • x) := by
      rw [← mul_smul, hcomm, mul_smul]
    rw [hstep, hiso (k ^ n) x ((c ^ j) • x)]
    exact hbdd j
  have hmem : ∀ j : ℤ, (c ^ j) ∈
      {k : G | dist ((g ^ n) • x) (k • ((g ^ n) • x)) ≤ B + 1 ∧
        dist ((h ^ n) • x) (k • ((h ^ n) • x)) ≤ B + 1} := by
    intro j
    exact ⟨le_trans (hmove g j hcg) (by linarith),
      le_trans (hmove h j hch) (by linarith)⟩
  have hinj : Function.Injective (fun j : ℤ => c ^ j) :=
    injective_zpow_iff_not_isOfFinOrder.mpr hfin
  exact Set.infinite_of_injective_forall_mem hinj hmem hfinite

/-- In a torsion-free ambient the same element is trivial.  So a compression
defect can only be suitable in an ambient where every nontrivial element
commuting with two of its independent loxodromics has an unbounded orbit. -/
theorem eq_one_of_commutes_of_bounded
    (hiso : IsIsometricAction G X) (hacy : IsAcylindrical G X)
    (htf : IsPowerTorsionFree G) {g h c : G} {x : X} (hg : IsLoxodromic g x)
    (hh : IsLoxodromic h x) (hind : Independent g h x) (hcg : Commute c g)
    (hch : Commute c h) {B : ℝ} (hbdd : ∀ j : ℤ, dist x ((c ^ j) • x) ≤ B) :
    c = 1 := by
  by_contra hc
  exact htf.not_isOfFinOrder hc
    (isOfFinOrder_of_commutes_of_bounded hiso hacy hg hh hind hcg hch hbdd)

/-- The same statement read off a suitable subgroup: if `S` is suitable and `c`
commutes with the two independent loxodromics that witness clause (2), then `c`
is trivial or moves the basepoint arbitrarily far. -/
theorem IsSuitable.unbounded_of_commutes {δ : ℝ} {S : Subgroup G} {x : X}
    (hs : IsSuitable δ S x) (htf : IsPowerTorsionFree G) {c : G} (hc : c ≠ 1) :
    ∀ g ∈ S, ∀ h ∈ S, IsLoxodromic g x → IsLoxodromic h x →
      Independent g h x → Commute c g → Commute c h →
      ∀ B : ℝ, ¬ ∀ j : ℤ, dist x ((c ^ j) • x) ≤ B := by
  intro g _ h _ hg hh hind hcg hch B hbdd
  exact hc (eq_one_of_commutes_of_bounded hs.isometric hs.acylindrical htf
    hg hh hind hcg hch hbdd)

/-! ## The remaining proposition, named

Everything above is a theorem.  What is not a theorem is that the compression
defect of some ambient group admits an action making it suitable, and that is a
single proposition, written here so that it can be pointed at. -/

/-- **The geometric half of Question 2**, as a proposition about one subgroup:
some hyperbolic space carries an acylindrical action of the ambient group in
which `N` is non-elementary.

This is the *only* thing `Sofic.ExplicitSuitableDefect` does not supply.  The
algebraic half, `HullSuitable.IsAlgebraicallySuitable N`, is proved there with
no hypotheses; `IsSuitable.toIsAlgebraicallySuitable` shows the two together are
Hull's Definition 1.4 and nothing more. -/
def HasSuitableGeometry (N : Subgroup G) : Prop :=
  ∃ (Y : Type u) (dY : PseudoMetricSpace Y) (aY : MulAction G Y) (δ : ℝ) (y : Y),
    @IsSuitable G _ Y dY aY δ N y

/-- **The exact division of labour.**  Supplying the geometry supplies the
algebra, and the algebra is supplied already.  So for the compression defects of
`Sofic.ExplicitSuitableDefect` the two halves of Hull's Definition 1.4 are in
different states, and this theorem says which implication connects them: the
geometric half implies the algebraic half, the algebraic half is proved with no
hypotheses, and nothing else stands between them and Hull's hypothesis. -/
theorem isAlgebraicallySuitable_of_hasSuitableGeometry {N : Subgroup G}
    (h : HasSuitableGeometry N) : HullSuitable.IsAlgebraicallySuitable N := by
  obtain ⟨Y, dY, aY, δ, y, hs⟩ := h
  exact @IsSuitable.toIsAlgebraicallySuitable G _ Y dY aY δ N y hs

end HullGeometry
end GroupApproximation
