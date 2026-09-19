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

That the particular ascending-HNN skeleton studied in this module admits an
action making its compression defect non-elementary.  With the definitions here
that is a single Lean proposition --- `IsSuitable δ N x` for the defect `N` and
some action --- and it remains unresolved for that skeleton.  It is not the
current manuscript's torsion-free existence question and is not needed by the
Fournier-Facio--Hull--Osin route now used there.  It is a
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
        -- `G` is a group, not commutative: what commutes here is `t` with its
        -- own powers, which is `Commute.refl` pushed through `pow_left`
        rw [pow_succ, ((Commute.refl t).pow_left n).eq]
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
        -- `G` is a group, not commutative: what commutes here is `t` with its
        -- own powers, which is `Commute.refl` pushed through `pow_left`
        rw [pow_succ, ((Commute.refl t).pow_left n).eq]
      have hstep : t ^ (n + 1) * p * (t ^ (n + 1))⁻¹
          = t * (t ^ n * p * (t ^ n)⁻¹) * t⁻¹ := by
        rw [hsplit, mul_inv_rev]
        simp only [mul_assoc]
      have hconj : t * p ^ (k ^ n) * t⁻¹ = (t * p * t⁻¹) ^ (k ^ n) := by
        simp
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
  -- the cast of `1` has to be reduced before `rfl` can see the two sides
  ⟨dist x ((g ^ 1) • x) / 1, ⟨1, by norm_num, by norm_num⟩⟩

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
  -- `sub` and `add (-c)` are the same function, but not the same term
  have hadd := Filter.tendsto_atTop_add_const_right Filter.atTop
    (-(2 * dist x y)) h
  simpa [sub_eq_add_neg] using hadd

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
  show dist x ((g ^ (m + n)) • x)
      ≤ dist x ((g ^ m) • x) + dist x ((g ^ n) • x)
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
  have hinv : (0:ℝ) ≤ ((n : ℝ))⁻¹ := by positivity
  simpa [div_eq_mul_inv, add_mul] using mul_le_mul_of_nonneg_right hstep hinv

/-- **Translation length is homogeneous.**  Passing to the subsequence
`n ↦ k n` in the limit above.  With `stableTranslation_mul_le` and
`stableTranslation_nonneg` this completes the seminorm: on the common
centralizer of two independent loxodromics, `stableTranslation` is a
homogeneous, subadditive, nonnegative function --- the data the translation
homomorphism is assembled from. -/
theorem stableTranslation_pow (hiso : IsIsometricAction G X) (g : G) (x : X)
    {k : ℕ} (hk : 0 < k) :
    stableTranslation (g ^ k) x = k * stableTranslation g x := by
  refine tendsto_nhds_unique (tendsto_stableTranslation hiso (g ^ k) x) ?_
  have hmul : Filter.Tendsto (fun n : ℕ => k * n) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono (fun n => Nat.le_mul_of_pos_left n hk)
      Filter.tendsto_id
  have h3 := (tendsto_stableTranslation hiso g x).comp hmul
  have h4 := h3.const_mul ((k : ℝ))
  refine h4.congr ?_
  intro n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hk0 : ((k : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
    have hn0 : ((n : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    have hkn : ((k * n : ℕ) : ℝ) = (k : ℝ) * (n : ℝ) := by push_cast; ring
    show (k : ℝ) * (dist x ((g ^ (k * n)) • x) / ((k * n : ℕ) : ℝ))
      = dist x (((g ^ k) ^ n) • x) / (n : ℝ)
    rw [← pow_mul, hkn]
    field_simp

/-! ### The quasi-axis

The Morse lemma is a statement *about* quasi-geodesics, so the first thing it
needs is one.  For a strongly loxodromic element the orbit map `k ↦ gᵏ x` is a
quasi-isometric embedding of the integers, and both of its bounds are already
proved: the upper one is `dist_pow_le`, the lower one is `mul_le_dist_pow`.  All
that is missing is the passage from `ℕ` to `ℤ`, which `dist_zpow_neg` supplies.

So the quasi-axis exists as soon as the translation length is positive.  What
the Morse lemma would add is that *every* quasi-geodesic with the same endpoints
stays uniformly close to it, and that is the step this development does not
have. -/

/-- The displacement of a power depends only on its absolute value. -/
theorem dist_zpow_natAbs (hiso : IsIsometricAction G X) (g : G) (x : X)
    (k : ℤ) : dist x ((g ^ k) • x) = dist x ((g ^ k.natAbs) • x) := by
  rcases le_or_gt 0 k with hk | hk
  · have hk' : ((k.natAbs : ℤ)) = k := Int.natAbs_of_nonneg hk
    rw [← zpow_natCast, hk']
  · have hk' : ((k.natAbs : ℤ)) = -k := by omega
    rw [← zpow_natCast, hk', dist_zpow_neg hiso]

/-- The upper quasi-geodesic bound, over the integers. -/
theorem dist_zpow_le (hiso : IsIsometricAction G X) (g : G) (x : X) (k : ℤ) :
    dist x ((g ^ k) • x) ≤ |(k : ℝ)| * dist x (g • x) := by
  rw [dist_zpow_natAbs hiso]
  have h := dist_pow_le hiso g x k.natAbs
  have hcast : ((k.natAbs : ℕ) : ℝ) = |(k : ℝ)| := by
    rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
  rw [hcast] at h
  exact h

/-- The lower quasi-geodesic bound, over the integers. -/
theorem mul_le_dist_zpow (hiso : IsIsometricAction G X) (g : G) (x : X)
    (k : ℤ) : stableTranslation g x * |(k : ℝ)| ≤ dist x ((g ^ k) • x) := by
  rw [dist_zpow_natAbs hiso]
  have h := mul_le_dist_pow g x k.natAbs
  have hcast : ((k.natAbs : ℕ) : ℝ) = |(k : ℝ)| := by
    rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
  rw [hcast] at h
  exact h

/-- Displacement between two orbit points depends only on the difference. -/
theorem dist_zpow_orbit (hiso : IsIsometricAction G X) (g : G) (x : X)
    (m n : ℤ) :
    dist ((g ^ m) • x) ((g ^ n) • x) = dist x ((g ^ (n - m)) • x) := by
  have h := hiso (g ^ m) x ((g ^ (n - m)) • x)
  rw [← mul_smul, ← zpow_add] at h
  have he : m + (n - m) = n := by ring
  rw [he] at h
  exact h

/-- **The quasi-axis.**  The orbit map of a group element is a
quasi-isometric embedding of the integers, with lower constant its translation
length and upper constant its displacement.  When the translation length is
positive --- that is, when the element is genuinely loxodromic --- both bounds
are effective, and the orbit is the quasi-geodesic the Morse lemma speaks
about. -/
theorem orbit_quasiIsometricEmbedding (hiso : IsIsometricAction G X) (g : G)
    (x : X) (m n : ℤ) :
    stableTranslation g x * |((n - m : ℤ) : ℝ)|
        ≤ dist ((g ^ m) • x) ((g ^ n) • x) ∧
      dist ((g ^ m) • x) ((g ^ n) • x)
        ≤ |((n - m : ℤ) : ℝ)| * dist x (g • x) := by
  rw [dist_zpow_orbit hiso]
  exact ⟨mul_le_dist_zpow hiso g x (n - m), dist_zpow_le hiso g x (n - m)⟩

/-! ### The chain lemma

The first lemma of every proof of quasi-geodesic stability, and the first one
here that is a genuine statement about hyperbolic spaces rather than about the
group: along a chain of points, the Gromov product of the endpoints is bounded
below by the smallest product of consecutive terms, at a cost of one `δ` per
step.  It is a direct induction on the four-point condition.

This is the estimate that turns local control into global control.  What it does
not yet give is *uniform* control: the loss is linear in the length of the
chain, and taming that --- to a logarithm by bisection, and then to a constant
by the Morse argument --- is the remaining work. -/

/-- **The chain lemma.**  If every consecutive Gromov product along a chain is
at least `c`, the endpoints' Gromov product is at least `c` less one `δ` per
step. -/
theorem gromovProduct_chain {δ : ℝ} (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ)
    (w : X) (y : ℕ → X) (c : ℝ) :
    ∀ N : ℕ, (∀ i, i < N + 1 → c ≤ gromovProduct (y i) (y (i + 1)) w) →
      c - N * δ ≤ gromovProduct (y 0) (y (N + 1)) w := by
  intro N
  induction N with
  | zero =>
      intro h
      simpa using h 0 (by norm_num)
  | succ n ih =>
      intro h
      have h1 : c - (n : ℝ) * δ ≤ gromovProduct (y 0) (y (n + 1)) w :=
        ih (fun i hi => h i (by omega))
      have h2 : c ≤ gromovProduct (y (n + 1)) (y (n + 1 + 1)) w :=
        h (n + 1) (by omega)
      have hnd : (0:ℝ) ≤ (n : ℝ) * δ := mul_nonneg (Nat.cast_nonneg n) hδ0
      have h5 : c - (n : ℝ) * δ ≤
          min (gromovProduct (y 0) (y (n + 1)) w)
            (gromovProduct (y (n + 1)) (y (n + 1 + 1)) w) := by
        refine le_min h1 ?_
        linarith
      have h3 := hδ w (y 0) (y (n + 1)) (y (n + 1 + 1))
      push_cast
      linarith

/-- The chain lemma along the orbit of a group element: consecutive orbit points
have Gromov product `(u k + u (k+1) - u 1) / 2`, so the endpoints' product is
bounded below by the smallest of those, less one `δ` per step. -/
theorem gromovProduct_orbit_chain {δ : ℝ} (hδ : IsHyperbolicSpace δ X)
    (hδ0 : 0 ≤ δ) (_hiso : IsIsometricAction G X) (g : G) (x : X) (c : ℝ)
    (N : ℕ)
    (hc : ∀ i, i < N + 1 →
      c ≤ gromovProduct ((g ^ i) • x) ((g ^ (i + 1)) • x) x) :
    c - N * δ ≤ gromovProduct ((g ^ (0:ℕ)) • x) ((g ^ (N + 1)) • x) x :=
  gromovProduct_chain hδ hδ0 x (fun n : ℕ => (g ^ n) • x) c N hc

/-- Consecutive orbit points, evaluated: the Gromov product of `gᵏ x` and
`gᵏ⁺¹ x` at `x` is `(d(x, gᵏ x) + d(x, gᵏ⁺¹ x) - d(x, g x)) / 2`.  Along a
genuinely loxodromic orbit both displacements grow at least linearly, so these
local products grow --- which is what the chain lemma consumes. -/
theorem gromovProduct_orbit_succ (hiso : IsIsometricAction G X) (g : G) (x : X)
    (k : ℕ) :
    gromovProduct ((g ^ k) • x) ((g ^ (k + 1)) • x) x
      = (dist x ((g ^ k) • x) + dist x ((g ^ (k + 1)) • x)
          - dist x (g • x)) / 2 := by
  have hstep : dist ((g ^ k) • x) ((g ^ (k + 1)) • x) = dist x (g • x) := by
    have h := hiso (g ^ k) x (g • x)
    rw [← mul_smul, ← pow_succ] at h
    rw [← h]
  simp only [gromovProduct, hstep, dist_comm ((g ^ k) • x) x,
    dist_comm ((g ^ (k + 1)) • x) x]

/-- **The chain lemma by bisection.**  Splitting a chain in half rather than
peeling one step at a time reduces the loss from one `δ` per step to one `δ` per
*halving*: over a chain of `2 ᵏ` steps the loss is `k · δ`, not `2 ᵏ · δ`.

This is the standard improvement, and it is the same induction run on a
different recursion: the two halves are chains of `2 ⁿ` steps, the inductive
hypothesis applies to each, and hyperbolicity joins them at one `δ`. -/
theorem gromovProduct_chain_pow_two {δ : ℝ} (hδ : IsHyperbolicSpace δ X)
    (hδ0 : 0 ≤ δ) (w : X) (c : ℝ) :
    ∀ (k : ℕ) (y : ℕ → X),
      (∀ i, i < 2 ^ k → c ≤ gromovProduct (y i) (y (i + 1)) w) →
        c - k * δ ≤ gromovProduct (y 0) (y (2 ^ k)) w := by
  intro k
  induction k with
  | zero =>
      intro y h
      simpa using h 0 (by norm_num)
  | succ n ih =>
      intro y h
      have hsplit : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by ring
      have h1 : c - (n : ℝ) * δ ≤ gromovProduct (y 0) (y (2 ^ n)) w :=
        ih y (fun i hi => h i (by rw [hsplit]; omega))
      have h2 : c - (n : ℝ) * δ
          ≤ gromovProduct (y (2 ^ n)) (y (2 ^ n + 2 ^ n)) w := by
        have hshift := ih (fun i => y (2 ^ n + i))
          (fun i hi => h (2 ^ n + i) (by rw [hsplit]; omega))
        simpa using hshift
      have hnd : (0:ℝ) ≤ (n : ℝ) * δ := mul_nonneg (Nat.cast_nonneg n) hδ0
      have h5 : c - (n : ℝ) * δ ≤
          min (gromovProduct (y 0) (y (2 ^ n)) w)
            (gromovProduct (y (2 ^ n)) (y (2 ^ n + 2 ^ n)) w) := le_min h1 h2
      have h3 := hδ w (y 0) (y (2 ^ n)) (y (2 ^ n + 2 ^ n))
      rw [hsplit]
      push_cast
      linarith

/-! ### Geodesics

The prerequisite the stability theorem needs and that nothing before it did.
`IsSuitable` is stated over a bare `PseudoMetricSpace`, because every clause of
Hull's Definition 1.4 and every theorem above is a statement about distances and
Gromov products alone.  Quasi-geodesic stability is not: it compares a
quasi-geodesic with an actual geodesic between its endpoints, so geodesics have
to exist.

They are introduced here as definitions with their elementary consequences,
including the one the comparison rests on --- a point on a geodesic between two
others has Gromov product zero there, which is the triangle equality. -/

/-- A geodesic segment, parametrised by arclength on `[a, b]`. -/
def IsGeodesicSegment (f : ℝ → X) (a b : ℝ) : Prop :=
  ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b, dist (f s) (f t) = |s - t|

/-- A geodesic space: any two points are joined by a geodesic segment. -/
def IsGeodesicSpace (X : Type v) [PseudoMetricSpace X] : Prop :=
  ∀ x y : X, ∃ f : ℝ → X,
    IsGeodesicSegment f 0 (dist x y) ∧ f 0 = x ∧ f (dist x y) = y

/-- A geodesic segment realises distances exactly: it is a quasi-geodesic with
constants `(1, 0)`, which is what makes it the comparison object. -/
theorem IsGeodesicSegment.dist_eq {f : ℝ → X} {a b : ℝ}
    (h : IsGeodesicSegment f a b) {s t : ℝ} (hs : s ∈ Set.Icc a b)
    (ht : t ∈ Set.Icc a b) : dist (f s) (f t) = |s - t| := h s hs t ht

theorem IsGeodesicSegment.dist_endpoints {f : ℝ → X} {a b : ℝ} (hab : a ≤ b)
    (h : IsGeodesicSegment f a b) : dist (f a) (f b) = b - a := by
  rw [h a ⟨le_refl a, hab⟩ b ⟨hab, le_refl b⟩,
    abs_of_nonpos (by linarith : a - b ≤ 0)]
  ring

/-- **The triangle equality along a geodesic.**  A point between `f a` and `f b`
sees them with Gromov product zero.  This is the fact the Morse comparison is
anchored on: it says a geodesic has no slack, so any excursion of a
quasi-geodesic away from it is measured against nothing. -/
theorem gromovProduct_eq_zero_of_mem_geodesic {f : ℝ → X} {a b s : ℝ}
    (hab : a ≤ b) (hs : s ∈ Set.Icc a b) (h : IsGeodesicSegment f a b) :
    gromovProduct (f a) (f b) (f s) = 0 := by
  obtain ⟨hsa, hsb⟩ := hs
  have h1 : dist (f a) (f s) = s - a := by
    rw [h a ⟨le_refl a, hab⟩ s ⟨hsa, hsb⟩,
      abs_of_nonpos (by linarith : a - s ≤ 0)]
    ring
  have h2 : dist (f b) (f s) = b - s := by
    rw [h b ⟨hab, le_refl b⟩ s ⟨hsa, hsb⟩,
      abs_of_nonneg (by linarith : (0:ℝ) ≤ b - s)]
  have h3 : dist (f a) (f b) = b - a := h.dist_endpoints hab
  simp only [gromovProduct, h1, h2, h3]
  ring

/-- **Properness of a centralizer, from one loxodromic.**  The two independent
loxodromics of `finite_commuting_ball` are more than the argument needs: a
single one suffices, because the pair `(g⁻ᴺ x, gᴺ x)` is already far apart --- at
distance `d(x, g²ᴺ x)` --- and every element commuting with `g` displaces both by
exactly its own displacement.

So the whole centralizer of a loxodromic, not just the common centralizer of an
independent pair, meets every ball in a finite set.  This is the properness
statement that Osin's elementary-closure theorem is about. -/
theorem finite_centralizer_ball (hiso : IsIsometricAction G X)
    (hacy : IsAcylindrical G X) {g : G} {x : X} (hg : IsLoxodromic g x)
    {ε : ℝ} (hε : 0 < ε) :
    {k : G | Commute k g ∧ dist x (k • x) ≤ ε}.Finite := by
  obtain ⟨R, N₀, hRN⟩ := hacy ε hε
  have hev := hg.eventually_ge_atTop R
  rw [Filter.eventually_atTop] at hev
  obtain ⟨M, hM⟩ := hev
  have hfar : R ≤ dist ((g ^ (-(M : ℤ))) • x) ((g ^ ((M : ℤ))) • x) := by
    rw [dist_zpow_orbit hiso]
    have he : ((M : ℤ)) - (-(M : ℤ)) = ((2 * M : ℕ) : ℤ) := by push_cast; ring
    rw [he, zpow_natCast]
    exact hM (2 * M) (by omega)
  obtain ⟨hfinite, -⟩ :=
    hRN ((g ^ (-(M : ℤ))) • x) ((g ^ ((M : ℤ))) • x) hfar
  refine Set.Finite.subset hfinite ?_
  rintro k ⟨hkg, hkx⟩
  have hmove : ∀ m : ℤ, dist ((g ^ m) • x) (k • ((g ^ m) • x)) ≤ ε := by
    intro m
    have hcomm : k * (g ^ m) = (g ^ m) * k := (hkg.zpow_right m).eq
    have hstep : k • ((g ^ m) • x) = (g ^ m) • (k • x) := by
      rw [← mul_smul, hcomm, mul_smul]
    rw [hstep, hiso (g ^ m) x (k • x)]
    exact hkx
  exact ⟨hmove _, hmove _⟩

/-- **The Gromov product is at most the distance to any point of a geodesic
joining its two arguments.**

Only the triangle inequality and the geodesic property are used --- no
hyperbolicity at all.  This matters because it is the tool that produces *upper*
bounds on Gromov products, and the four-point condition never does: read in
either direction, `min (x|y) (y|z) - δ ≤ (x|z)` bounds a product from **below**.
Every attempt in this development to control a product from above by
hyperbolicity alone failed for exactly that reason, and this lemma is where the
control has to come from instead.

The estimate is the triangle inequality twice: `d(f a, w) ≤ (s - a) + d(f s, w)`
and `d(f b, w) ≤ (b - s) + d(f s, w)`, added, with `d(f a, f b) = b - a`
subtracted. -/
theorem gromovProduct_le_dist_of_mem_geodesic {f : ℝ → X} {a b s : ℝ}
    (hab : a ≤ b) (hs : s ∈ Set.Icc a b) (h : IsGeodesicSegment f a b) (w : X) :
    gromovProduct (f a) (f b) w ≤ dist w (f s) := by
  obtain ⟨hsa, hsb⟩ := hs
  have h1 : dist (f a) (f s) = s - a := by
    rw [h a ⟨le_refl a, hab⟩ s ⟨hsa, hsb⟩,
      abs_of_nonpos (by linarith : a - s ≤ 0)]
    ring
  have h2 : dist (f b) (f s) = b - s := by
    rw [h b ⟨hab, le_refl b⟩ s ⟨hsa, hsb⟩,
      abs_of_nonneg (by linarith : (0:ℝ) ≤ b - s)]
  have h3 : dist (f a) (f b) = b - a := h.dist_endpoints hab
  have t1 : dist (f a) w ≤ dist (f a) (f s) + dist (f s) w :=
    dist_triangle _ _ _
  have t2 : dist (f b) w ≤ dist (f b) (f s) + dist (f s) w :=
    dist_triangle _ _ _
  simp only [gromovProduct, h3]
  rw [dist_comm w (f s)]
  linarith

/-! ### The converse: the Gromov product *is* the distance to the geodesic

The previous lemma bounds `(A|C)_w` above by the distance to any point of a
geodesic joining `A` to `C`, using no hyperbolicity.  The converse --- that some
point of that geodesic is within `(A|C)_w + 2δ` of `w` --- is the hyperbolic
direction, and it does follow from the four-point condition, at the specific
point of the geodesic at distance `d(A,w) − (A|C)_w` from `A`.

The reason it works is an exact computation rather than an estimate: at that
point `p`, the two Gromov products `(A|p)_w` and `(p|C)_w` are *equal*, both to
`(d(w,p) + (A|C)_w) / 2`.  So the `min` in the four-point condition is that
common value, and the condition reads

    (d(w,p) + t) / 2 − δ ≤ t,   i.e.   d(w,p) ≤ t + 2δ,

with `t = (A|C)_w`.  No excursion argument and no bootstrap: one application of
hyperbolicity at the right point. -/

/-- The hyperbolic direction, at the distinguished point of the geodesic. -/
theorem dist_le_gromovProduct_add {δ : ℝ} (hδ : IsHyperbolicSpace δ X)
    {f : ℝ → X} {A C : X} (hf : IsGeodesicSegment f 0 (dist A C))
    (hA : f 0 = A) (hC : f (dist A C) = C) (w : X) {s : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ dist A C)
    (hsdef : 2 * s = dist A w - dist C w + dist A C) :
    dist w (f s) ≤ gromovProduct A C w + 2 * δ := by
  have hACnonneg : (0:ℝ) ≤ dist A C := dist_nonneg
  have hAs : dist A (f s) = s := by
    have h := hf 0 ⟨le_refl 0, hACnonneg⟩ s ⟨hs0, hs1⟩
    rw [hA] at h
    rw [h, abs_of_nonpos (by linarith : (0:ℝ) - s ≤ 0)]
    ring
  have hCs : dist C (f s) = dist A C - s := by
    have h := hf (dist A C) ⟨hACnonneg, le_refl _⟩ s ⟨hs0, hs1⟩
    rw [hC] at h
    rw [h, abs_of_nonneg (by linarith : (0:ℝ) ≤ dist A C - s)]
  have hAp : gromovProduct A (f s) w
      = (dist w (f s) + gromovProduct A C w) / 2 := by
    simp only [gromovProduct, hAs, dist_comm (f s) w]
    linarith
  have hCp : gromovProduct (f s) C w
      = (dist w (f s) + gromovProduct A C w) / 2 := by
    simp only [gromovProduct, dist_comm (f s) C, hCs, dist_comm (f s) w]
    linarith
  have h4 := hδ w A (f s) C
  rw [hAp, hCp, min_self] at h4
  linarith

/-- **The Gromov product is the distance to the geodesic, up to `2δ`.**  Some
point of a geodesic joining `A` to `C` lies within `(A|C)_w + 2δ` of `w`.

With `gromovProduct_le_dist_of_mem_geodesic` this pins the Gromov product to the
distance from `w` to the geodesic on both sides, which is the dictionary the
Morse argument is written in. -/
theorem exists_mem_geodesic_dist_le {δ : ℝ} (hδ : IsHyperbolicSpace δ X)
    {f : ℝ → X} {A C : X} (hf : IsGeodesicSegment f 0 (dist A C))
    (hA : f 0 = A) (hC : f (dist A C) = C) (w : X) :
    ∃ s ∈ Set.Icc (0:ℝ) (dist A C),
      dist w (f s) ≤ gromovProduct A C w + 2 * δ := by
  have htri1 : dist C w ≤ dist A C + dist A w := by
    have h := dist_triangle C A w
    rwa [dist_comm C A] at h
  have htri2 : dist A w ≤ dist A C + dist C w := dist_triangle A C w
  refine ⟨(dist A w - dist C w + dist A C) / 2, ⟨by linarith, by linarith⟩, ?_⟩
  exact dist_le_gromovProduct_add hδ hf hA hC w (by linarith) (by linarith)
    (by ring)

/-- **The dictionary, both ways.**  The Gromov product `(A|C)_w` is a lower
bound for the distance from `w` to every point of a geodesic joining `A` to `C`,
and some point of that geodesic is within `2δ` of it.  So `(A|C)_w` *is* the
distance from `w` to the geodesic, to within `2δ`.

This is the translation the Morse argument is carried out in: a statement about
how far a quasi-geodesic strays from a geodesic becomes a statement about how
large its Gromov products are, and vice versa. -/
theorem gromovProduct_dist_geodesic {δ : ℝ} (hδ : IsHyperbolicSpace δ X)
    {f : ℝ → X} {A C : X} (hf : IsGeodesicSegment f 0 (dist A C))
    (hA : f 0 = A) (hC : f (dist A C) = C) (w : X) :
    (∀ s ∈ Set.Icc (0:ℝ) (dist A C), gromovProduct A C w ≤ dist w (f s)) ∧
      ∃ s ∈ Set.Icc (0:ℝ) (dist A C),
        dist w (f s) ≤ gromovProduct A C w + 2 * δ :=
  -- the lemma speaks of the geodesic's own endpoints; `hA` and `hC` say those
  -- are `A` and `C`
  ⟨fun _ hs => by
      have h := gromovProduct_le_dist_of_mem_geodesic dist_nonneg hs hf w
      rwa [hA, hC] at h,
    exists_mem_geodesic_dist_le hδ hf hA hC w⟩

/-! ### Fellow-travelling of geodesics

Osin, *Acylindrically hyperbolic groups*, Lemma 2.3(b): two geodesics out of the
same point stay `4δ`-close for as long as the Gromov product of their far
endpoints allows.  The source states it and cites Coornaert--Delzant--
Papadopoulos; the derivation below is from the four-point condition directly and
lands on the same constant.

The argument is three applications of hyperbolicity and one identity.  On a
geodesic from `x` to `y`, the point at distance `t` from `x` has
`(f t | y)_x = t` exactly.  So `(y | h t)_x ≥ min((y|z)_x, (z|h t)_x) − δ ≥ t − δ`
and then `(f t | h t)_x ≥ min((f t|y)_x, (y|h t)_x) − δ ≥ t − 2δ`, whence
`d(f t, h t) = 2t − 2(f t|h t)_x ≤ 4δ`. -/

theorem gromovProduct_comm (x y w : X) :
    gromovProduct x y w = gromovProduct y x w := by
  simp only [gromovProduct, dist_comm x y]
  ring

/-- On a geodesic from `x` to `y`, the point at distance `t` from `x` has
Gromov product exactly `t` with the far endpoint. -/
theorem gromovProduct_geodesic_point {f : ℝ → X} {x y : X} {t : ℝ}
    (hf : IsGeodesicSegment f 0 (dist x y)) (hfx : f 0 = x)
    (hfy : f (dist x y) = y) (ht0 : 0 ≤ t) (hty : t ≤ dist x y) :
    gromovProduct (f t) y x = t := by
  have hxy : (0:ℝ) ≤ dist x y := dist_nonneg
  have h1 : dist x (f t) = t := by
    have h := hf 0 ⟨le_refl 0, hxy⟩ t ⟨ht0, hty⟩
    rw [hfx] at h
    rw [h, abs_of_nonpos (by linarith : (0:ℝ) - t ≤ 0)]
    ring
  have h2 : dist y (f t) = dist x y - t := by
    have h := hf (dist x y) ⟨hxy, le_refl _⟩ t ⟨ht0, hty⟩
    rw [hfy] at h
    rw [h, abs_of_nonneg (by linarith : (0:ℝ) ≤ dist x y - t)]
  simp only [gromovProduct, dist_comm (f t) x, dist_comm y x, h1,
    dist_comm (f t) y, h2]
  ring

/-- **Fellow-travelling** (Osin, Lemma 2.3(b)).  Two geodesics leaving `x`
towards `y` and `z` stay `4δ`-close up to distance `(y|z)_x`. -/
theorem dist_le_four_delta_of_le_gromovProduct {δ : ℝ}
    (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ) {f h : ℝ → X} {x y z : X}
    (hf : IsGeodesicSegment f 0 (dist x y)) (hfx : f 0 = x)
    (hfy : f (dist x y) = y)
    (hh : IsGeodesicSegment h 0 (dist x z)) (hhx : h 0 = x)
    (hhz : h (dist x z) = z) {t : ℝ} (ht0 : 0 ≤ t) (hty : t ≤ dist x y)
    (htz : t ≤ dist x z) (htg : t ≤ gromovProduct y z x) :
    dist (f t) (h t) ≤ 4 * δ := by
  have hfu : gromovProduct (f t) y x = t :=
    gromovProduct_geodesic_point hf hfx hfy ht0 hty
  have hhv : gromovProduct (h t) z x = t :=
    gromovProduct_geodesic_point hh hhx hhz ht0 htz
  have hzv : gromovProduct z (h t) x = t := by
    rw [gromovProduct_comm]; exact hhv
  have hyv : t - δ ≤ gromovProduct y (h t) x := by
    have h4 := hδ x y z (h t)
    rw [hzv] at h4
    have hmin : t ≤ min (gromovProduct y z x) t := le_min htg (le_refl t)
    linarith
  have huv : t - 2 * δ ≤ gromovProduct (f t) (h t) x := by
    have h4 := hδ x (f t) y (h t)
    rw [hfu] at h4
    have hmin : t - δ ≤ min t (gromovProduct y (h t) x) :=
      le_min (by linarith) hyv
    linarith
  have hdx : dist x (f t) = t := by
    have hxy : (0:ℝ) ≤ dist x y := dist_nonneg
    have hg := hf 0 ⟨le_refl 0, hxy⟩ t ⟨ht0, hty⟩
    rw [hfx] at hg
    rw [hg, abs_of_nonpos (by linarith : (0:ℝ) - t ≤ 0)]
    ring
  have hdz : dist x (h t) = t := by
    have hxz : (0:ℝ) ≤ dist x z := dist_nonneg
    have hg := hh 0 ⟨le_refl 0, hxz⟩ t ⟨ht0, htz⟩
    rw [hhx] at hg
    rw [hg, abs_of_nonpos (by linarith : (0:ℝ) - t ≤ 0)]
    ring
  simp only [gromovProduct, dist_comm (f t) x, dist_comm (h t) x, hdx,
    hdz] at huv
  linarith

/-! ### Towards Osin's Lemma 3.6

Osin's Lemma 3.6 strengthens acylindricity: the second condition is relaxed from
`d(y, gy) ≤ ε` to `d(y, gy) ≤ d(x,y) + ε`, which is a much weaker requirement, and
the conclusion is unchanged.  Its proof is given in full in the source and rests
on Lemma 2.3(b) --- proved above --- applied twice, at `x` and at `g y`.

This section builds the pieces.  Two are bookkeeping about geodesics; the third
is the displacement estimate that feeds the first application. -/

/-- Reversing a geodesic segment. -/
theorem IsGeodesicSegment.reverse {f : ℝ → X} {L : ℝ}
    (h : IsGeodesicSegment f 0 L) :
    IsGeodesicSegment (fun t => f (L - t)) 0 L := by
  intro s hs t ht
  obtain ⟨hs0, hsL⟩ := hs
  obtain ⟨ht0, htL⟩ := ht
  have hd := h (L - s) ⟨by linarith, by linarith⟩ (L - t) ⟨by linarith, by linarith⟩
  have heq : L - s - (L - t) = t - s := by ring
  rw [hd, heq, abs_sub_comm]

/-- The image of a geodesic segment under the action is a geodesic segment. -/
theorem IsGeodesicSegment.smul (hiso : IsIsometricAction G X) (g : G)
    {f : ℝ → X} {L : ℝ} (h : IsGeodesicSegment f 0 L) :
    IsGeodesicSegment (fun t => g • f t) 0 L := by
  intro s hs t ht
  rw [hiso g (f s) (f t)]
  exact h s hs t ht

/-- **The displacement estimate.**  If `k` moves `x` by at most `ε` and moves `y`
by at most `d(x,y) + ε`, then `y` and `k y` have Gromov product at least
`d(x,y)/2 − ε` at `x`.

This is the first step of Osin's Lemma 3.6, and it is pure triangle inequality:
`k` being an isometry forces `|d(x, k y) − d(x, y)| ≤ d(x, k x) ≤ ε`, and the
Gromov product then unwinds. -/
theorem gromovProduct_lower_of_displacement (hiso : IsIsometricAction G X)
    {x y : X} {k : G} {ε : ℝ} (hk1 : dist x (k • x) ≤ ε)
    (hk2 : dist y (k • y) ≤ dist x y + ε) :
    dist x y / 2 - ε ≤ gromovProduct y (k • y) x := by
  have hiso' : dist (k • x) (k • y) = dist x y := hiso k x y
  have hupper : dist x (k • y) ≤ dist x y + ε := by
    have h1 : dist x (k • y) ≤ dist x (k • x) + dist (k • x) (k • y) :=
      dist_triangle _ _ _
    rw [hiso'] at h1
    linarith
  have hlower : dist x y - ε ≤ dist x (k • y) := by
    have h1 : dist (k • x) (k • y) ≤ dist (k • x) x + dist x (k • y) :=
      dist_triangle _ _ _
    rw [hiso', dist_comm (k • x) x] at h1
    linarith
  simp only [gromovProduct, dist_comm y x, dist_comm (k • y) x]
  linarith

/-- **The first comparison of Lemma 3.6.**  Under the displacement hypotheses, a
geodesic from `x` to `y` and a geodesic from `x` to `k y` stay `4δ`-close out to
distance `d(x,y)/2 − ε`.

This is `dist_le_four_delta_of_le_gromovProduct` fed by
`gromovProduct_lower_of_displacement`, and it is the step that puts the point
`m` of Osin's proof within `4δ` of the point `n`. -/
theorem dist_geodesic_comparison_le {δ : ℝ} (hδ : IsHyperbolicSpace δ X)
    (hδ0 : 0 ≤ δ) (hiso : IsIsometricAction G X) {x y : X} {k : G} {ε : ℝ}
    (hk1 : dist x (k • x) ≤ ε) (hk2 : dist y (k • y) ≤ dist x y + ε)
    {p q : ℝ → X} (hp : IsGeodesicSegment p 0 (dist x y)) (hp0 : p 0 = x)
    (hp1 : p (dist x y) = y)
    (hq : IsGeodesicSegment q 0 (dist x (k • y))) (hq0 : q 0 = x)
    (hq1 : q (dist x (k • y)) = k • y) {t : ℝ} (ht0 : 0 ≤ t)
    (hty : t ≤ dist x y) (htz : t ≤ dist x (k • y))
    (htg : t ≤ dist x y / 2 - ε) :
    dist (p t) (q t) ≤ 4 * δ := by
  refine dist_le_four_delta_of_le_gromovProduct hδ hδ0 hp hp0 hp1 hq hq0 hq1
    ht0 hty htz ?_
  exact le_trans htg (gromovProduct_lower_of_displacement hiso hk1 hk2)

/-- **The second comparison, and the estimate of Osin's Lemma 3.6.**

If `k` moves `x` by at most `ε` and moves `y` by at most `d(x,y) + ε`, and `R₀`
satisfies `2ε ≤ R₀` and `3R₀ ≤ d(x,y)`, then `k` moves the point of a geodesic
`[x,y]` at distance `R₀` from `x` by at most `8δ + ε`.

The source's route gives `16δ + ε`; the constant here is better because the last
step collapses.  Osin bounds `d(k m, k')` by `d(x, k x) + d(m, k')`, going
through the triangle inequality; but `k m` and `k'` are both on the *same*
geodesic --- the image of `[x,y]` under `k` --- at parameters `R₀` and
`d(x,y) − d(x, k y) + R₀`, so their distance is exactly
`|d(x, k y) − d(x, y)| ≤ ε`.

The two applications of `dist_le_four_delta_of_le_gromovProduct` are at `x`,
comparing `[x,y]` with `[x, k y]`, and at `k y`, comparing `[k y, x]` with
`[k y, k x]`. -/
theorem dist_smul_geodesic_point_le {δ : ℝ} (hδ : IsHyperbolicSpace δ X)
    (hδ0 : 0 ≤ δ) (hiso : IsIsometricAction G X) {x y : X} {k : G} {ε R₀ : ℝ}
    (hε : 0 < ε) (hR₀ε : 2 * ε ≤ R₀) (hxy : 3 * R₀ ≤ dist x y)
    (hk1 : dist x (k • x) ≤ ε) (hk2 : dist y (k • y) ≤ dist x y + ε)
    {p q : ℝ → X} (hp : IsGeodesicSegment p 0 (dist x y)) (hp0 : p 0 = x)
    (hp1 : p (dist x y) = y)
    (hq : IsGeodesicSegment q 0 (dist x (k • y))) (hq0 : q 0 = x)
    (hq1 : q (dist x (k • y)) = k • y) :
    dist (p R₀) (k • (p R₀)) ≤ 8 * δ + ε := by
  have hR₀pos : (0:ℝ) < R₀ := by linarith
  have hisoxy : dist (k • x) (k • y) = dist x y := hiso k x y
  have hupper : dist x (k • y) ≤ dist x y + ε := by
    have h1 : dist x (k • y) ≤ dist x (k • x) + dist (k • x) (k • y) :=
      dist_triangle _ _ _
    rw [hisoxy] at h1
    linarith
  have hlower : dist x y - ε ≤ dist x (k • y) := by
    have h1 : dist (k • x) (k • y) ≤ dist (k • x) x + dist x (k • y) :=
      dist_triangle _ _ _
    rw [hisoxy, dist_comm (k • x) x] at h1
    linarith
  have hR₀le : R₀ ≤ dist x y := by linarith
  have hR₀le' : R₀ ≤ dist x (k • y) := by linarith
  -- first comparison, at x
  have hmn : dist (p R₀) (q R₀) ≤ 4 * δ :=
    dist_geodesic_comparison_le hδ hδ0 hiso hk1 hk2 hp hp0 hp1 hq hq0 hq1
      (le_of_lt hR₀pos) hR₀le hR₀le' (by linarith)
  -- the two geodesics out of k • y
  have hyx : dist (k • y) x = dist x (k • y) := dist_comm _ _
  have hykx : dist (k • y) (k • x) = dist x y := by
    rw [hiso k y x, dist_comm y x]
  have hq'geo : IsGeodesicSegment
      (fun t => q (dist x (k • y) - t)) 0 (dist (k • y) x) := by
    rw [hyx]
    exact hq.reverse
  have hq'0 : (fun t => q (dist x (k • y) - t)) 0 = k • y := by
    show q (dist x (k • y) - 0) = k • y
    rw [sub_zero, hq1]
  have hq'1 : (fun t => q (dist x (k • y) - t)) (dist (k • y) x) = x := by
    show q (dist x (k • y) - dist (k • y) x) = x
    rw [hyx, sub_self, hq0]
  have hgp : IsGeodesicSegment (fun t => k • p t) 0 (dist x y) :=
    hp.smul hiso k
  have hg'geo : IsGeodesicSegment
      (fun t => k • p (dist x y - t)) 0 (dist (k • y) (k • x)) := by
    rw [hykx]
    exact hgp.reverse
  have hg'0 : (fun t => k • p (dist x y - t)) 0 = k • y := by
    show k • p (dist x y - 0) = k • y
    rw [sub_zero, hp1]
  have hg'1 : (fun t => k • p (dist x y - t)) (dist (k • y) (k • x)) = k • x := by
    show k • p (dist x y - dist (k • y) (k • x)) = k • x
    rw [hykx, sub_self, hp0]
  -- second comparison, at k • y
  have ht'0 : (0:ℝ) ≤ dist x (k • y) - R₀ := by linarith
  have ht'1 : dist x (k • y) - R₀ ≤ dist (k • y) x := by rw [hyx]; linarith
  have ht'2 : dist x (k • y) - R₀ ≤ dist (k • y) (k • x) := by
    rw [hykx]; linarith
  have ht'g : dist x (k • y) - R₀ ≤ gromovProduct x (k • x) (k • y) := by
    simp only [gromovProduct, dist_comm (k • x) (k • y),
      dist_comm x (k • y)]
    linarith
  have hnk := dist_le_four_delta_of_le_gromovProduct hδ hδ0 hq'geo hq'0 hq'1
    hg'geo hg'0 hg'1 ht'0 ht'1 ht'2 ht'g
  have harg : dist x (k • y) - (dist x (k • y) - R₀) = R₀ := by ring
  rw [harg] at hnk
  -- assemble
  have hmk : dist (p R₀) (k • p (dist x y - (dist x (k • y) - R₀))) ≤ 8 * δ := by
    have ht := dist_triangle (p R₀) (q R₀)
      (k • p (dist x y - (dist x (k • y) - R₀)))
    linarith
  have hσ0 : (0:ℝ) ≤ dist x y - (dist x (k • y) - R₀) := by linarith
  have hσ1 : dist x y - (dist x (k • y) - R₀) ≤ dist x y := by linarith
  have hpar : dist (k • (p R₀))
      (k • p (dist x y - (dist x (k • y) - R₀))) ≤ ε := by
    rw [hiso k (p R₀) (p (dist x y - (dist x (k • y) - R₀)))]
    rw [hp R₀ ⟨le_of_lt hR₀pos, hR₀le⟩
      (dist x y - (dist x (k • y) - R₀)) ⟨hσ0, hσ1⟩]
    have heq : R₀ - (dist x y - (dist x (k • y) - R₀))
        = dist x (k • y) - dist x y := by ring
    rw [heq, abs_le]
    constructor <;> linarith
  have hfin := dist_triangle (p R₀)
    (k • p (dist x y - (dist x (k • y) - R₀))) (k • (p R₀))
  rw [dist_comm (k • p (dist x y - (dist x (k • y) - R₀))) (k • (p R₀))] at hfin
  linarith

/-- **Osin's Lemma 3.6.**  Acylindricity with the second condition relaxed from
`d(y, k y) ≤ ε` to `d(y, k y) ≤ d(x,y) + ε`.

The relaxed condition is much weaker --- it permits `k` to move `y` by almost the
whole diameter of the configuration --- and the conclusion is the same finiteness.
The proof is the estimate above applied at the point of a geodesic `[x,y]` at
distance `R₀` from `x`: every `k` satisfying the relaxed conditions moves that
point by at most `8δ + ε`, so the whole set embeds in one acylindricity set for
the pair `(x, p R₀)`. -/
theorem acylindrical_relaxed {δ : ℝ} (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ)
    (hiso : IsIsometricAction G X) (hgeo : IsGeodesicSpace X)
    (hacy : IsAcylindrical G X) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, ∀ x y : X, R ≤ dist x y →
      {k : G | dist x (k • x) ≤ ε ∧ dist y (k • y) ≤ dist x y + ε}.Finite := by
  obtain ⟨R₀', N, hRN⟩ := hacy (8 * δ + ε) (by linarith)
  refine ⟨3 * max R₀' (2 * ε), ?_⟩
  intro x y hxy
  set R₀ := max R₀' (2 * ε) with hR₀def
  have hR₀' : R₀' ≤ R₀ := le_max_left _ _
  have hR₀ε : 2 * ε ≤ R₀ := le_max_right _ _
  have hR₀pos : (0:ℝ) < R₀ := by linarith
  have hxy' : 3 * R₀ ≤ dist x y := hxy
  obtain ⟨p, hp, hp0, hp1⟩ := hgeo x y
  have hR₀le : R₀ ≤ dist x y := by linarith
  have hxm : dist x (p R₀) = R₀ := by
    have hg := hp 0 ⟨le_refl 0, dist_nonneg⟩ R₀ ⟨le_of_lt hR₀pos, hR₀le⟩
    rw [hp0] at hg
    rw [hg, abs_of_nonpos (by linarith : (0:ℝ) - R₀ ≤ 0)]
    ring
  obtain ⟨hfin, -⟩ := hRN x (p R₀) (by rw [hxm]; exact hR₀')
  refine Set.Finite.subset hfin ?_
  rintro k ⟨hk1, hk2⟩
  obtain ⟨q, hq, hq0, hq1⟩ := hgeo x (k • y)
  exact ⟨by linarith, dist_smul_geodesic_point_le hδ hδ0 hiso hε hR₀ε hxy'
    hk1 hk2 hp hp0 hp1 hq hq0 hq1⟩

/-! ## What is not here, and why it is not a declaration

There is no predicate in this module asserting that the particular ambient
group's compression defect admits an action making it suitable.  No theorem of
this corpus concludes that skeleton-specific statement, and a `def … : Prop`
that nothing concludes is exactly the shape
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
