import GroupApproximation.Sofic.HullSuitableDefectSubgroup
import Mathlib.Analysis.Subadditive

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
`IsSuitable δ N x` for the defect `N` and some action --- and it is the geometric half
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
noncomputable def gromovProduct (x y w : X) : ℝ :=
  (dist x w + dist y w - dist x y) / 2

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

/-- **Properness of a common centralizer.**  Under an acylindrical action with
two independent loxodromics, only finitely many elements commuting with both
move the basepoint by at most `ε`.

This is the reusable core of the constraint: an element commuting with `g` moves
every point of the `g`-orbit by exactly its own displacement, so acylindricity
applied to two far-apart orbit points confines the whole common centralizer's
`ε`-ball to one finite set.  It is also the first thing Osin's
elementary-closure theorem needs. -/
theorem finite_commuting_ball (hiso : IsIsometricAction G X)
    (hacy : IsAcylindrical G X) {g h : G} {x : X} (hg : IsLoxodromic g x)
    (hind : Independent g h x) {ε : ℝ} (hε : 0 < ε) :
    {k : G | Commute k g ∧ Commute k h ∧ dist x (k • x) ≤ ε}.Finite := by
  obtain ⟨R, N₀, hRN⟩ := hacy ε hε
  obtain ⟨n, hn⟩ := exists_far_apart hg hind R
  obtain ⟨hfinite, -⟩ := hRN ((g ^ n) • x) ((h ^ n) • x) hn
  refine Set.Finite.subset hfinite ?_
  rintro k ⟨hkg, hkh, hkx⟩
  have hmove : ∀ z : G, Commute k z →
      dist ((z ^ n) • x) (k • ((z ^ n) • x)) ≤ ε := by
    intro z hkz
    have hcomm : k * (z ^ n) = (z ^ n) * k := (hkz.pow_right n).eq
    have hstep : k • ((z ^ n) • x) = (z ^ n) • (k • x) := by
      rw [← mul_smul, hcomm, mul_smul]
    rw [hstep, hiso (z ^ n) x (k • x)]
    exact hkx
  exact ⟨hmove g hkg, hmove h hkh⟩

/-- **An element with bounded orbit commuting with two independent loxodromics
has finite order.**

This is the constraint a suitable geometry places on the ambient group, and it
is proved from the definitions: `c` commutes with `g` and `h`, so it moves every
point of both orbits by exactly `dist x (c • x)`; acylindricity applied to two
points of those orbits that are far apart then confines all the powers of `c`
to one finite set, and an infinite-order element has infinitely many powers. -/
theorem isOfFinOrder_of_commutes_of_bounded
    (hiso : IsIsometricAction G X) (hacy : IsAcylindrical G X)
    {g h c : G} {x : X} (hg : IsLoxodromic g x) (_hh : IsLoxodromic h x)
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

/-- **A subgroup with a nontrivial centralizing element of bounded orbit is
never suitable**, over a torsion-free ambient.  This is what rules out the
obvious candidate: the *compressed copy* `u ι(Γ) u⁻¹` of a compression datum is
centralized by the transported root, which is nontrivial by the datum's own
`witness_commutator_ne_one`.  So the suitable subgroup of a compression pattern
cannot be the compressed copy, and has to be sought in the defect --- which is
where `Sofic.HullSuitableDefectSubgroup` puts it. -/
theorem not_isSuitable_of_centralizing {δ : ℝ} {S : Subgroup G} {x : X}
    (htf : IsPowerTorsionFree G) {c : G} (hc : c ≠ 1)
    (hcomm : ∀ y ∈ S, Commute c y) {B : ℝ}
    (hbdd : ∀ j : ℤ, dist x ((c ^ j) • x) ≤ B) :
    ¬ IsSuitable δ S x := by
  intro hs
  obtain ⟨g, hgS, h, hhS, hg, hh, hind⟩ := hs.nonElementary
  exact hc (eq_one_of_commutes_of_bounded hs.isometric hs.acylindrical htf
    hg hh hind (hcomm g hgS) (hcomm h hhS) hbdd)

/-! ## The compression relation forbids genuine loxodromy

`IsLoxodromic` above asks only that the power orbit escape every bounded set,
which is the weakest reading.  The quantitative form --- the orbit map bounded
below by a linear function --- is the one the literature means, and it is the
one a compression relation destroys.

A compression `t p t⁻¹ = p ^ k` with `2 ≤ k` makes the orbit of `p` grow at most
*linearly in `j`* along the exponentially sparse subsequence `k ^ j`, because
`p ^ (k ^ j)` is a conjugate of `p` by `t ^ j` and conjugating by `t ^ j` costs
at most `j` displacements of `t`, twice.  A logarithmic orbit is not bounded
below by a linear one.

This is the first step of the route that would refute suitability for a
compression pattern outright: it settles the compressed direction, where the
Baumslag--Solitar relation lives.  It does not settle the defect, whose elements
are not powers of `p`. -/

/-- The quantitative form of loxodromy: the orbit map is bounded below by a
linear function.  This is what "loxodromic" means in the literature, and it
implies `IsLoxodromic`. -/
def IsStronglyLoxodromic (g : G) (x : X) : Prop :=
  ∃ l : ℝ, 0 < l ∧ ∀ n : ℕ, l * n ≤ dist x ((g ^ n) • x)

theorem isLoxodromic_of_isStronglyLoxodromic {g : G} {x : X}
    (h : IsStronglyLoxodromic g x) : IsLoxodromic g x := by
  obtain ⟨l, hl, hle⟩ := h
  exact Filter.tendsto_atTop_mono hle
    (Filter.Tendsto.const_mul_atTop hl tendsto_natCast_atTop_atTop)

/-- Displacement is subadditive along powers. -/
theorem dist_pow_le (hiso : IsIsometricAction G X) (t : G) (x : X) :
    ∀ j : ℕ, dist x ((t ^ j) • x) ≤ j * dist x (t • x) := by
  intro j
  induction j with
  | zero => simp
  | succ n ih =>
      have hsplit : t ^ (n + 1) = t * t ^ n := by
        rw [pow_succ, mul_comm]
      have hstep : dist x ((t ^ (n + 1)) • x)
          ≤ dist x (t • x) + dist x ((t ^ n) • x) := by
        rw [hsplit, mul_smul]
        refine le_trans (dist_triangle x (t • x) (t • ((t ^ n) • x))) ?_
        rw [hiso t x ((t ^ n) • x)]
      push_cast
      linarith

/-- Conjugating by a power of the stable letter costs at most that many
displacements of the stable letter, twice. -/
theorem dist_conj_le (hiso : IsIsometricAction G X) (t p : G) (x : X) (j : ℕ) :
    dist x ((t ^ j * p * (t ^ j)⁻¹) • x)
      ≤ 2 * (j : ℝ) * dist x (t • x) + dist x (p • x) := by
  have hsm : (t ^ j * p * (t ^ j)⁻¹) • x
      = (t ^ j) • (p • (((t ^ j)⁻¹) • x)) := by
    rw [mul_smul, mul_smul]
  have hinvdist : dist x (((t ^ j)⁻¹) • x) = dist x ((t ^ j) • x) := by
    have h := hiso (t ^ j) x (((t ^ j)⁻¹) • x)
    rw [← mul_smul, mul_inv_cancel, one_smul] at h
    rw [← h, dist_comm]
  have hA : dist x ((t ^ j) • (p • (((t ^ j)⁻¹) • x)))
      ≤ dist x ((t ^ j) • x) + dist x (p • (((t ^ j)⁻¹) • x)) := by
    refine le_trans
      (dist_triangle x ((t ^ j) • x) ((t ^ j) • (p • (((t ^ j)⁻¹) • x)))) ?_
    rw [hiso (t ^ j) x (p • (((t ^ j)⁻¹) • x))]
  have hB : dist x (p • (((t ^ j)⁻¹) • x))
      ≤ dist x (p • x) + dist x ((t ^ j) • x) := by
    refine le_trans (dist_triangle x (p • x) (p • (((t ^ j)⁻¹) • x))) ?_
    rw [hiso p x (((t ^ j)⁻¹) • x), hinvdist]
  have hC := dist_pow_le hiso t x j
  rw [hsm]
  linarith

/-- The compression relation, iterated: `t ^ j` conjugates `p` to `p ^ (k ^ j)`.
-/
theorem conj_pow_eq {t p : G} {k : ℕ} (h : t * p * t⁻¹ = p ^ k) :
    ∀ j : ℕ, t ^ j * p * (t ^ j)⁻¹ = p ^ (k ^ j) := by
  intro j
  induction j with
  | zero => simp
  | succ n ih =>
      have hsplit : t ^ (n + 1) = t * t ^ n := by
        rw [pow_succ, mul_comm]
      have hstep : t ^ (n + 1) * p * (t ^ (n + 1))⁻¹
          = t * (t ^ n * p * (t ^ n)⁻¹) * t⁻¹ := by
        rw [hsplit, mul_inv_rev]
        simp only [mul_assoc]
      have hconj : t * p ^ (k ^ n) * t⁻¹ = (t * p * t⁻¹) ^ (k ^ n) := by
        simpa [MulAut.conj_apply] using map_pow (MulAut.conj t) p (k ^ n)
      rw [hstep, ih, hconj, h, ← pow_mul, pow_succ, mul_comm k (k ^ n)]

/-- **A compressed element is never genuinely loxodromic.**  If
`t p t⁻¹ = p ^ k` with `2 ≤ k`, the orbit of `p` grows at most linearly in `j`
along the exponentially sparse subsequence `k ^ j`, so no linear lower bound can
survive.  Every compression datum whose source copy is cyclic carries exactly
such a relation, by `CompressionSourceData.not_conjugation_surjective`. -/
theorem not_isStronglyLoxodromic_of_compression (hiso : IsIsometricAction G X)
    {t p : G} {k : ℕ} (hk : 2 ≤ k) (h : t * p * t⁻¹ = p ^ k) (x : X) :
    ¬ IsStronglyLoxodromic p x := by
  rintro ⟨l, hl, hle⟩
  set D := dist x (t • x) with hD
  set E := dist x (p • x) with hE
  have hD0 : (0:ℝ) ≤ D := dist_nonneg
  have hE0 : (0:ℝ) ≤ E := dist_nonneg
  obtain ⟨j, hj⟩ := exists_nat_gt (max ((4 * D + E) / l) 1)
  have hjr : (1:ℝ) < (j : ℝ) := lt_of_le_of_lt (le_max_right _ _) hj
  have hjd : (4 * D + E) / l < (j : ℝ) := lt_of_le_of_lt (le_max_left _ _) hj
  have hlj : 4 * D + E < (j : ℝ) * l := (div_lt_iff₀ hl).mp hjd
  -- the orbit is small along the sparse subsequence
  have hbig := hle (k ^ (2 * j))
  rw [← conj_pow_eq h (2 * j)] at hbig
  have hsmall := dist_conj_le hiso t p x (2 * j)
  have hcastsmall : 2 * ((2 * j : ℕ) : ℝ) * D + E = 4 * (j : ℝ) * D + E := by
    push_cast
    ring
  rw [hcastsmall] at hsmall
  -- but the subsequence is exponentially sparse
  have hpow : j ^ 2 < k ^ (2 * j) := by
    have hself : ∀ m : ℕ, m < 2 ^ m := by
      intro m
      induction m with
      | zero => norm_num
      | succ n ih =>
          have hone : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by norm_num)
          have htwo : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by ring
          omega
    have h1 : j < 2 ^ j := hself j
    have h2 : j ^ 2 < (2 ^ j) ^ 2 := Nat.pow_lt_pow_left h1 (by norm_num)
    have h3 : (2 ^ j) ^ 2 = 2 ^ (2 * j) := by
      rw [← pow_mul, mul_comm]
    have h4 : (2:ℕ) ^ (2 * j) ≤ k ^ (2 * j) := Nat.pow_le_pow_left hk _
    calc j ^ 2 < (2 ^ j) ^ 2 := h2
      _ = 2 ^ (2 * j) := h3
      _ ≤ k ^ (2 * j) := h4
  have hcast : ((j : ℝ)) ^ 2 < ((k ^ (2 * j) : ℕ) : ℝ) := by
    exact_mod_cast hpow
  have hgrow : l * ((j : ℝ)) ^ 2 < l * ((k ^ (2 * j) : ℕ) : ℝ) :=
    mul_lt_mul_of_pos_left hcast hl
  have hquad : 4 * (j : ℝ) * D + E < l * ((j : ℝ)) ^ 2 := by
    have hstep : (4 * D + E) * (j : ℝ) < ((j : ℝ) * l) * (j : ℝ) :=
      mul_lt_mul_of_pos_right hlj (by linarith)
    nlinarith [hstep, hE0, hjr]
  linarith

/-! ## Translation length

The first component of the machinery that would decide suitability outright.
`stableTranslation` is the infimum of `d(x, gⁿ x) / n` over positive `n` --- the
Fekete limit of the same sequence, but taken as an infimum so that no
subadditivity argument is needed for the two facts that matter: it bounds the
orbit from below, and it is positive exactly when the element is genuinely
loxodromic.

Together with `not_isStronglyLoxodromic_of_compression` this reads: a compressed
element has translation length zero. -/

/-- The stable translation length of `g` at `x`. -/
noncomputable def stableTranslation (g : G) (x : X) : ℝ :=
  sInf {r : ℝ | ∃ n : ℕ, 0 < n ∧ r = dist x ((g ^ n) • x) / n}

theorem stableTranslation_set_nonempty (g : G) (x : X) :
    {r : ℝ | ∃ n : ℕ, 0 < n ∧ r = dist x ((g ^ n) • x) / n}.Nonempty :=
  ⟨dist x ((g ^ 1) • x) / 1, ⟨1, by norm_num, rfl⟩⟩

theorem stableTranslation_set_bddBelow (g : G) (x : X) :
    BddBelow {r : ℝ | ∃ n : ℕ, 0 < n ∧ r = dist x ((g ^ n) • x) / n} := by
  refine ⟨0, ?_⟩
  rintro r ⟨n, hn, rfl⟩
  exact div_nonneg dist_nonneg (Nat.cast_nonneg n)

theorem stableTranslation_nonneg (g : G) (x : X) :
    0 ≤ stableTranslation g x := by
  refine le_csInf (stableTranslation_set_nonempty g x) ?_
  rintro r ⟨n, hn, rfl⟩
  exact div_nonneg dist_nonneg (Nat.cast_nonneg n)

theorem stableTranslation_le (g : G) (x : X) {n : ℕ} (hn : 0 < n) :
    stableTranslation g x ≤ dist x ((g ^ n) • x) / n :=
  csInf_le (stableTranslation_set_bddBelow g x) ⟨n, hn, rfl⟩

/-- The translation length bounds the orbit from below. -/
theorem mul_le_dist_pow (g : G) (x : X) (n : ℕ) :
    stableTranslation g x * n ≤ dist x ((g ^ n) • x) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn' : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn
    have h := stableTranslation_le g x hn
    rw [le_div_iff₀ hn'] at h
    exact h

/-- **Genuine loxodromy is positive translation length.** -/
theorem isStronglyLoxodromic_iff_pos (g : G) (x : X) :
    IsStronglyLoxodromic g x ↔ 0 < stableTranslation g x := by
  constructor
  · rintro ⟨l, hl, hle⟩
    refine lt_of_lt_of_le hl (le_csInf (stableTranslation_set_nonempty g x) ?_)
    rintro r ⟨n, hn, rfl⟩
    have hn' : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn
    rw [le_div_iff₀ hn']
    exact hle n
  · intro h
    exact ⟨stableTranslation g x, h, mul_le_dist_pow g x⟩

/-- **A compressed element has translation length zero.** -/
theorem stableTranslation_eq_zero_of_compression (hiso : IsIsometricAction G X)
    {t p : G} {k : ℕ} (hk : 2 ≤ k) (h : t * p * t⁻¹ = p ^ k) (x : X) :
    stableTranslation p x = 0 := by
  by_contra hne
  refine not_isStronglyLoxodromic_of_compression hiso hk h x ?_
  refine (isStronglyLoxodromic_iff_pos p x).mpr ?_
  exact lt_of_le_of_ne (stableTranslation_nonneg p x) (Ne.symm hne)

/-- Loxodromy does not depend on the basepoint. -/
theorem isLoxodromic_of_isLoxodromic (hiso : IsIsometricAction G X) {g : G}
    {x y : X} (h : IsLoxodromic g x) : IsLoxodromic g y := by
  have hbound : ∀ n : ℕ,
      dist x ((g ^ n) • x) - 2 * dist x y ≤ dist y ((g ^ n) • y) := by
    intro n
    have h1 : dist x ((g ^ n) • x)
        ≤ dist x y + dist y ((g ^ n) • y) + dist ((g ^ n) • y) ((g ^ n) • x) :=
      le_trans (dist_triangle x y ((g ^ n) • x))
        (by linarith [dist_triangle y ((g ^ n) • y) ((g ^ n) • x)])
    have h2 : dist ((g ^ n) • y) ((g ^ n) • x) = dist y x := hiso (g ^ n) y x
    rw [h2, dist_comm y x] at h1
    linarith
  refine Filter.tendsto_atTop_mono hbound ?_
  simpa using Filter.tendsto_atTop_add_const_right Filter.atTop
    (-(2 * dist x y)) h

/-! ### The translation length is a limit, and a seminorm on a centralizer

`stableTranslation` was defined as an infimum, which is all the two facts above
need.  It is also the Fekete limit of the same sequence, and that is what makes
it behave like a length: Mathlib's `Subadditive.tendsto_lim` applies because the
displacement sequence `n ↦ d(x, gⁿ x)` is subadditive, and `Subadditive.lim` is
by definition the same infimum.

The payoff is `stableTranslation_mul_le`: on a set of pairwise commuting
elements the translation length is subadditive, and together with the
homogeneity that the same limit argument gives it is a seminorm.  That is the
object the translation homomorphism `C(g) → ℝ` is built from. -/

/-- The displacement sequence of a group element is subadditive. -/
theorem subadditive_dist_pow (hiso : IsIsometricAction G X) (g : G) (x : X) :
    Subadditive (fun n : ℕ => dist x ((g ^ n) • x)) := by
  intro m n
  have h1 : (g ^ (m + n)) • x = (g ^ m) • ((g ^ n) • x) := by
    rw [pow_add, mul_smul]
  rw [h1]
  refine le_trans (dist_triangle x ((g ^ m) • x) ((g ^ m) • ((g ^ n) • x))) ?_
  rw [hiso (g ^ m) x ((g ^ n) • x)]

theorem bddBelow_dist_pow_div (g : G) (x : X) :
    BddBelow (Set.range fun n : ℕ => dist x ((g ^ n) • x) / n) := by
  refine ⟨0, ?_⟩
  rintro r ⟨n, rfl⟩
  exact div_nonneg dist_nonneg (Nat.cast_nonneg n)

/-- The infimum definition agrees with Mathlib's Fekete limit. -/
theorem stableTranslation_eq_lim (hiso : IsIsometricAction G X) (g : G) (x : X) :
    stableTranslation g x = (subadditive_dist_pow hiso g x).lim := by
  unfold stableTranslation Subadditive.lim
  congr 1
  ext r
  simp only [Set.mem_setOf_eq, Set.mem_image, Set.mem_Ici]
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, hn, rfl⟩
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, hn, rfl⟩

/-- **The translation length is the limit of the normalised displacement.** -/
theorem tendsto_stableTranslation (hiso : IsIsometricAction G X) (g : G) (x : X) :
    Filter.Tendsto (fun n : ℕ => dist x ((g ^ n) • x) / n) Filter.atTop
      (nhds (stableTranslation g x)) := by
  rw [stableTranslation_eq_lim hiso]
  exact (subadditive_dist_pow hiso g x).tendsto_lim (bddBelow_dist_pow_div g x)

/-- **Translation length is subadditive on commuting elements.**  With
`stableTranslation_nonneg` this makes it a seminorm on any abelian subgroup ---
in particular on the common centralizer of two independent loxodromics, which is
where the translation homomorphism lives. -/
theorem stableTranslation_mul_le (hiso : IsIsometricAction G X) {a b : G}
    (hab : Commute a b) (x : X) :
    stableTranslation (a * b) x
      ≤ stableTranslation a x + stableTranslation b x := by
  refine le_of_tendsto_of_tendsto (tendsto_stableTranslation hiso (a * b) x)
    ((tendsto_stableTranslation hiso a x).add
      (tendsto_stableTranslation hiso b x)) ?_
  filter_upwards with n
  have hpow : (a * b) ^ n = a ^ n * b ^ n := hab.mul_pow n
  have hsm : ((a * b) ^ n) • x = (a ^ n) • ((b ^ n) • x) := by
    rw [hpow, mul_smul]
  have hstep : dist x (((a * b) ^ n) • x)
      ≤ dist x ((a ^ n) • x) + dist x ((b ^ n) • x) := by
    rw [hsm]
    refine le_trans (dist_triangle x ((a ^ n) • x) ((a ^ n) • ((b ^ n) • x))) ?_
    rw [hiso (a ^ n) x ((b ^ n) • x)]
  have hn : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  rw [div_add_div_same]
  exact div_le_div_of_nonneg_right hstep hn

/-! ## What is not here, and why it is not a declaration

There is no predicate in this module asserting that some ambient group's
compression defect admits an action making it suitable.  That statement is the
geometric half of the manuscript's Question 2, no theorem of this corpus
concludes it, and a `def … : Prop` that nothing concludes is exactly the shape
`scripts/check_non_mf_unconditional.py` flags as a literature stand-in --- its
`open-predicate` detector is that test.  Writing one here would put a
placeholder for an open problem into the library under the name of a
definition, which is the thing this repository's own audit exists to prevent.

So the open question lives where open questions belong: in
`notes/HULL_ROUTING_AUDIT_2026-08-16.md`, whose addenda record what is proved,
what is not, and what each direction would need.  Everything in this module is a
definition with proved consequences or a theorem with a closed proof, and
nothing anywhere in `Sofic.HullSuitableDefectSubgroup`,
`Sofic.ExplicitSuitableDefect` or this file is conditional on the missing
geometry: the objects those modules build are closed terms.

`IsSuitable.toIsAlgebraicallySuitable` is the whole of the relation between the
two halves.  A suitable subgroup is algebraically suitable; the algebraic half
is exhibited with no hypotheses; and the theorems above say what the geometric
half forbids --- a nontrivial centralizing element of bounded orbit, and any
genuine loxodromy in a compressed direction. -/

end HullGeometry
end GroupApproximation
