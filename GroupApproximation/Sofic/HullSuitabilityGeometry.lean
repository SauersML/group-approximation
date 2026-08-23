import GroupApproximation.Sofic.HullSuitableDefectSubgroup
import Mathlib.Analysis.Subadditive
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Nat.Log

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
* `IsEscaping g x` --- the orbit of `x` under positive powers of `g` escapes
  every bounded set.
* `IsLoxodromic g x` --- that orbit has a positive linear lower bound, up to
  an additive constant.
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

open scoped commutatorElement

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

theorem gromovProduct_nonneg (y z w : X) : 0 ≤ gromovProduct y z w := by
  have h := dist_triangle y w z
  rw [dist_comm w z] at h
  unfold gromovProduct
  linarith

theorem gromovProduct_comm (x y w : X) :
    gromovProduct x y w = gromovProduct y x w := by
  simp only [gromovProduct, dist_comm x y]
  ring

/-- The Gromov product is invariant under an isometric group action. -/
theorem gromovProduct_smul (hiso : IsIsometricAction G X) (a : G)
    (y z w : X) :
    gromovProduct (a • y) (a • z) (a • w) = gromovProduct y z w := by
  unfold gromovProduct
  rw [hiso a y w, hiso a z w, hiso a y z]

/-- Moving the first endpoint changes the Gromov product by at most the
distance moved. -/
theorem gromovProduct_le_add_dist_left (y y' z w : X) :
    gromovProduct y z w ≤ gromovProduct y' z w + dist y y' := by
  have h1 : dist y w ≤ dist y y' + dist y' w := dist_triangle y y' w
  have h2 : dist y' z ≤ dist y' y + dist y z := dist_triangle y' y z
  unfold gromovProduct
  rw [dist_comm y' y] at h2
  linarith

/-- Moving the second endpoint changes the Gromov product by at most the
distance moved. -/
theorem gromovProduct_le_add_dist_right (y z z' w : X) :
    gromovProduct y z w ≤ gromovProduct y z' w + dist z z' := by
  have h1 : dist z w ≤ dist z z' + dist z' w := dist_triangle z z' w
  have h2 : dist y z' ≤ dist y z + dist z z' := dist_triangle y z z'
  unfold gromovProduct
  linarith

/-- Moving the basepoint changes the Gromov product by at most the distance
moved. -/
theorem gromovProduct_le_add_dist_base (y z w w' : X) :
    gromovProduct y z w ≤ gromovProduct y z w' + dist w w' := by
  have h1 : dist y w ≤ dist y w' + dist w' w := dist_triangle y w' w
  have h2 : dist z w ≤ dist z w' + dist w' w := dist_triangle z w' w
  unfold gromovProduct
  rw [dist_comm w' w] at h1 h2
  linarith

/-- The complementary Gromov products based at the two ends of a segment add
up to the length of that segment. -/
theorem gromovProduct_add_swap_base (a b c : X) :
    gromovProduct a b c + gromovProduct a c b = dist b c := by
  unfold gromovProduct
  rw [dist_comm a c, dist_comm a b, dist_comm c b]
  ring

/-- Gromov's four-point condition. -/
def IsHyperbolicSpace (δ : ℝ) (X : Type v) [PseudoMetricSpace X] : Prop :=
  ∀ w x y z : X,
    min (gromovProduct x y w) (gromovProduct y z w) - δ ≤ gromovProduct x z w

/-- The upper-bound form of the four-point inequality.  If `(a|b)_w` is more
than `δ` larger than `(b|c)_w`, then `(a|c)_w` is at most
`(b|c)_w + δ`. -/
theorem gromovProduct_le_add_delta_of_lt {δ : ℝ}
    (hδ : IsHyperbolicSpace δ X) {a b c w : X}
    (hfar : gromovProduct b c w + δ < gromovProduct a b w) :
    gromovProduct a c w ≤ gromovProduct b c w + δ := by
  by_contra hnot
  have hac : gromovProduct b c w + δ < gromovProduct a c w :=
    lt_of_not_ge hnot
  have h4 := hδ w b a c
  rw [gromovProduct_comm b a w] at h4
  have hmin : gromovProduct b c w + δ <
      min (gromovProduct a b w) (gromovProduct a c w) :=
    lt_min hfar hac
  linarith

/-- One step of the bounded-backtracking induction.  A previous global
backtracking bound, one long edge, and one bounded local turn give both linear
progress across the edge and the same global bound at the next vertex. -/
theorem chain_progress_step {δ C L : ℝ} (hδ : IsHyperbolicSpace δ X)
    (hgap : 2 * (C + δ) < L) {o p q r : X}
    (hprevious : gromovProduct o q p ≤ C + δ)
    (hedge : L ≤ dist p q) (hlocal : gromovProduct p r q ≤ C) :
    dist o p + (L - 2 * (C + δ)) ≤ dist o q ∧
      gromovProduct o r q ≤ C + δ := by
  constructor
  · unfold gromovProduct at hprevious
    rw [dist_comm q p] at hprevious
    linarith
  · have hswap := gromovProduct_add_swap_base o p q
    have hbehind : C + δ < gromovProduct o p q := by
      linarith
    have hfar : gromovProduct p r q + δ < gromovProduct o p q := by
      linarith
    have hnext := gromovProduct_le_add_delta_of_lt hδ hfar
    linarith

/-- The weak escape property: the positive power orbit eventually leaves every
bounded set.  This is strictly weaker than genuine loxodromy and is retained
under an explicit name only for lemmas that use no quantitative geometry. -/
def IsEscaping (g : G) (x : X) : Prop :=
  Filter.Tendsto (fun n : ℕ => dist x ((g ^ n) • x)) Filter.atTop Filter.atTop

/-- `g` and `h` are independent at `x` when the Gromov products of their power
orbits stay bounded. -/
def Independent (g h : G) (x : X) : Prop :=
  ∃ C : ℝ, ∀ n m : ℤ, gromovProduct ((g ^ n) • x) ((h ^ m) • x) x ≤ C

/-- Genuine loxodromy: the orbit map has a positive linear lower bound, up to
an additive constant.  Together with `dist_pow_le`, this is precisely a
quasi-isometric embedding of the nonnegative integers.  The additive constant
makes the notion transparently invariant under basepoint changes and
conjugation, as required by Morse stability. -/
def IsLoxodromic (g : G) (x : X) : Prop :=
  ∃ l : ℝ, 0 < l ∧ ∃ B : ℝ, 0 ≤ B ∧
    ∀ n : ℕ, l * n - B ≤ dist x ((g ^ n) • x)

/-- Genuine loxodromy implies weak escape. -/
theorem IsLoxodromic.isEscaping {g : G} {x : X}
    (h : IsLoxodromic g x) : IsEscaping g x := by
  obtain ⟨l, hl, B, _hB, hle⟩ := h
  rw [IsEscaping, Filter.tendsto_atTop]
  intro A
  obtain ⟨N, hN⟩ := exists_nat_gt ((A + B) / l)
  rw [Filter.eventually_atTop]
  refine ⟨N, fun n hn => ?_⟩
  have hcast : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hdiv : (A + B) / l < (n : ℝ) := lt_of_lt_of_le hN hcast
  have hlin : A + B < l * (n : ℝ) := by
    rw [div_lt_iff₀ hl] at hdiv
    linarith
  exact le_of_lt (lt_of_lt_of_le (by linarith) (hle n))

/-- **Two-axis ping-pong from the two cross-backtracking bounds.**

Let `p = A B`.  The orbit path is refined by the intermediate vertices
`pᵏ A x`.  Its two kinds of local turns are isometric translates of exactly

* `(A⁻¹x | Bx)_x`, and
* `(B⁻¹x | Ax)_x`.

If both are bounded by `C` and both syllables have length at least
`L > 2(C+δ)`, `chain_progress_step` applied twice per power gives
`d(x,pᵏx) ≥ 2k(L-2(C+δ))`. -/
theorem isLoxodromic_mul_of_cross_backtracking {δ C L : ℝ}
    (hδ : IsHyperbolicSpace δ X) (hiso : IsIsometricAction G X)
    {A B : G} {x : X} (hCδ : 0 ≤ C + δ)
    (hgap : 2 * (C + δ) < L)
    (hA : L ≤ dist x (A • x)) (hB : L ≤ dist x (B • x))
    (hAB : gromovProduct (A⁻¹ • x) (B • x) x ≤ C)
    (hBA : gromovProduct (B⁻¹ • x) (A • x) x ≤ C) :
    IsLoxodromic (A * B) x := by
  let p : G := A * B
  let q : ℝ := L - 2 * (C + δ)
  have hq : 0 < q := by dsimp [q]; linarith
  have hodd : ∀ k : ℕ,
      gromovProduct ((p ^ k) • x) ((p ^ (k + 1)) • x)
        ((p ^ k * A) • x) ≤ C := by
    intro k
    let t : G := (p ^ k * A)⁻¹
    have ht0 : t * p ^ k = A⁻¹ := by
      dsimp [t]
      group
    have ht1 : t * p ^ (k + 1) = B := by
      dsimp [t, p]
      rw [pow_succ]
      group
    have htbase : t * (p ^ k * A) = 1 := by
      dsimp [t]
      group
    have h := gromovProduct_smul hiso t ((p ^ k) • x)
      ((p ^ (k + 1)) • x) ((p ^ k * A) • x)
    rw [← mul_smul, ht0, ← mul_smul, ht1, ← mul_smul, htbase, one_smul] at h
    rw [← h]
    exact hAB
  have heven : ∀ k : ℕ,
      gromovProduct ((p ^ k * A) • x) ((p ^ (k + 1) * A) • x)
        ((p ^ (k + 1)) • x) ≤ C := by
    intro k
    let t : G := (p ^ (k + 1))⁻¹
    have ht0 : t * (p ^ k * A) = B⁻¹ := by
      dsimp [t, p]
      rw [pow_succ]
      group
    have ht1 : t * (p ^ (k + 1) * A) = A := by
      dsimp [t]
      group
    have htbase : t * p ^ (k + 1) = 1 := by
      dsimp [t]
      group
    have h := gromovProduct_smul hiso t ((p ^ k * A) • x)
      ((p ^ (k + 1) * A) • x) ((p ^ (k + 1)) • x)
    rw [← mul_smul, ht0, ← mul_smul, ht1, ← mul_smul, htbase, one_smul] at h
    rw [← h]
    exact hBA
  have hind : ∀ k : ℕ,
      q * (2 * k) ≤ dist x ((p ^ k) • x) ∧
        gromovProduct x ((p ^ k * A) • x) ((p ^ k) • x) ≤ C + δ := by
    intro k
    induction k with
    | zero =>
        constructor
        · simp
        · have hz : gromovProduct x (A • x) x = 0 := by
            unfold gromovProduct
            rw [dist_self, dist_comm (A • x) x]
            ring
          simpa [p] using le_trans (le_of_eq hz) hCδ
    | succ k ih =>
        have hedgeA : L ≤ dist ((p ^ k) • x) ((p ^ k * A) • x) := by
          have h := hiso (p ^ k) x (A • x)
          rw [← mul_smul] at h
          rw [h]
          exact hA
        have hedgeB :
            L ≤ dist ((p ^ k * A) • x) ((p ^ (k + 1)) • x) := by
          have h := hiso (p ^ k * A) x (B • x)
          have hpnext : (p ^ k * A) * B = p ^ (k + 1) := by
            dsimp [p]
            rw [pow_succ]
            group
          rw [← mul_smul, hpnext] at h
          rw [h]
          exact hB
        have hstepA := chain_progress_step hδ hgap ih.2 hedgeA (hodd k)
        have hstepB := chain_progress_step hδ hgap hstepA.2 hedgeB (heven k)
        constructor
        · have hprev := ih.1
          have hprogA := hstepA.1
          have hprogB := hstepB.1
          dsimp [q] at hprev hprogA hprogB ⊢
          push_cast
          linarith
        · simpa only [Nat.succ_eq_add_one] using hstepB.2
  refine ⟨2 * q, by positivity, 0, le_rfl, ?_⟩
  intro k
  have hk := (hind k).1
  nlinarith

/-- **The independent-axes branch.**  Two independent loxodromics have a
loxodromic product of sufficiently large equal powers.

Independence supplies both cross-backtracking bounds uniformly for all integer
powers.  Loxodromy makes the two syllable lengths exceed the fixed threshold
`2(C+δ)+1`; the preceding two-axis ping-pong theorem then applies. -/
theorem exists_isLoxodromic_mul_pow_of_independent {δ : ℝ}
    (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ)
    (hiso : IsIsometricAction G X) {a b : G} {x : X}
    (ha : IsLoxodromic a x) (hb : IsLoxodromic b x)
    (hind : Independent a b x) :
    ∃ N : ℕ, IsLoxodromic ((a ^ N) * (b ^ N)) x := by
  obtain ⟨C₀, hC₀⟩ := hind
  let C : ℝ := max C₀ 0
  let L : ℝ := 2 * (C + δ) + 1
  have hC₀C : C₀ ≤ C := le_max_left _ _
  have hC0 : 0 ≤ C := le_max_right _ _
  have hCδ : 0 ≤ C + δ := add_nonneg hC0 hδ0
  have hgap : 2 * (C + δ) < L := by dsimp [L]; linarith
  have hea := ha.isEscaping.eventually_ge_atTop L
  have heb := hb.isEscaping.eventually_ge_atTop L
  rw [Filter.eventually_atTop] at hea heb
  obtain ⟨Na, hNa⟩ := hea
  obtain ⟨Nb, hNb⟩ := heb
  let N : ℕ := max Na Nb
  have hAN : L ≤ dist x ((a ^ N) • x) := hNa N (le_max_left _ _)
  have hBN : L ≤ dist x ((b ^ N) • x) := hNb N (le_max_right _ _)
  have hAB :
      gromovProduct ((a ^ N)⁻¹ • x) ((b ^ N) • x) x ≤ C := by
    have h := hC₀ (-(N : ℤ)) (N : ℤ)
    simpa only [zpow_neg, zpow_natCast] using le_trans h hC₀C
  have hBA :
      gromovProduct ((b ^ N)⁻¹ • x) ((a ^ N) • x) x ≤ C := by
    have h := hC₀ (N : ℤ) (-(N : ℤ))
    have h' :
        gromovProduct ((b ^ (-(N : ℤ))) • x) ((a ^ (N : ℤ)) • x) x ≤ C := by
      rw [gromovProduct_comm]
      exact le_trans h hC₀C
    simpa only [zpow_neg, zpow_natCast] using h'
  refine ⟨N, ?_⟩
  exact isLoxodromic_mul_of_cross_backtracking
    hδ hiso hCδ hgap hAN hBN hAB hBA

/-! ## Acylindricity -/

/-- Osin's acylindricity condition for a group action on a metric space. -/
def IsAcylindrical (G : Type u) (X : Type v) [Group G] [PseudoMetricSpace X]
    [MulAction G X] : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ (R : ℝ) (N : ℕ), ∀ x y : X, R ≤ dist x y →
    {g : G | dist x (g • x) ≤ ε ∧ dist y (g • y) ≤ ε}.Finite ∧
      {g : G | dist x (g • x) ≤ ε ∧ dist y (g • y) ≤ ε}.ncard ≤ N

/-- **The acylindrical common-power pigeonhole step.**

Suppose the `N + 1` difference elements

`g⁻ᵃⁱ hᵇⁱ`

all move the same two sufficiently distant points by at most `ε`.  Acylindricity
says that at most `N` elements can do this, so two difference elements agree.
If both exponent lists are injective, cancelling that equality gives a genuine
common nonzero power of `g` and `h`.

This is the exact finite pigeonhole conclusion consumed after Morse stability
has converted long fellow-travelling axes into the two displacement bounds. -/
theorem acylindrical_common_power_pigeonhole
    (hacy : IsAcylindrical G X) {ε : ℝ} (hε : 0 < ε) :
    ∃ (R : ℝ) (N : ℕ), ∀ (x y : X), R ≤ dist x y →
      ∀ (g h : G) (a b : Fin (N + 1) → ℤ),
        Function.Injective a → Function.Injective b →
        (∀ i, dist x ((g ^ (-a i) * h ^ (b i)) • x) ≤ ε ∧
          dist y ((g ^ (-a i) * h ^ (b i)) • y) ≤ ε) →
        ∃ i j : Fin (N + 1), i ≠ j ∧
          a i - a j ≠ 0 ∧ b i - b j ≠ 0 ∧
          g ^ (a i - a j) = h ^ (b i - b j) := by
  classical
  obtain ⟨R, N, hRN⟩ := hacy ε hε
  refine ⟨R, N, fun x y hxy g h a b ha hb hmove => ?_⟩
  let K : Set G := {k : G |
    dist x (k • x) ≤ ε ∧ dist y (k • y) ≤ ε}
  obtain ⟨hKfinite, hKcard⟩ := hRN x y hxy
  letI : Fintype K := hKfinite.fintype
  let d : Fin (N + 1) → K := fun i =>
    ⟨g ^ (-a i) * h ^ (b i), hmove i⟩
  have hcard : Fintype.card K < Fintype.card (Fin (N + 1)) := by
    rw [Set.fintypeCard_eq_ncard, Fintype.card_fin]
    dsimp [K]
    omega
  obtain ⟨i, j, hij, hdij⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt d hcard
  have heq : g ^ (-a i) * h ^ (b i) = g ^ (-a j) * h ^ (b j) :=
    congrArg Subtype.val hdij
  have hpower : g ^ (a i - a j) = h ^ (b i - b j) := by
    calc
      g ^ (a i - a j) =
          g ^ (a i) * (g ^ (-a j) * h ^ (b j)) * h ^ (-b j) := by
            group
      _ = g ^ (a i) * (g ^ (-a i) * h ^ (b i)) * h ^ (-b j) := by
            exact (congrArg
              (fun z : G => g ^ (a i) * z * h ^ (-b j)) heq).symm
      _ = h ^ (b i - b j) := by group
  refine ⟨i, j, hij, ?_, ?_, hpower⟩
  · intro hz
    apply hij
    apply ha
    omega
  · intro hz
    apply hij
    apply hb
    omega

/-- The displacement of a difference element is exactly the distance between
the corresponding two orbit points. -/
theorem dist_zpow_difference (hiso : IsIsometricAction G X)
    (g h : G) (a b : ℤ) (z : X) :
    dist z ((g ^ (-a) * h ^ b) • z) =
      dist ((g ^ a) • z) ((h ^ b) • z) := by
  have hd := hiso (g ^ a) z ((g ^ (-a) * h ^ b) • z)
  have hcancel : g ^ a * (g ^ (-a) * h ^ b) = h ^ b := by group
  rw [← mul_smul, hcancel] at hd
  exact hd.symm

/-- A uniform bounded-cancellation estimate for difference words implies
independence.  This is the direct interface used by normal-form arguments:
after rewriting the distance between two orbit points as the displacement of
`g⁻ᵃhᵇ`, the defining Gromov product is bounded by half the cancellation
constant. -/
theorem independent_of_difference_lower
    (hiso : IsIsometricAction G X) {g h : G} {x : X} (C : ℝ)
    (hdiff : ∀ a b : ℤ,
      dist x ((g ^ a) • x) + dist x ((h ^ b) • x) - C ≤
        dist x ((g ^ (-a) * h ^ b) • x)) :
    Independent g h x := by
  refine ⟨C / 2, ?_⟩
  intro a b
  have hlower := hdiff a b
  rw [dist_zpow_difference hiso] at hlower
  unfold gromovProduct
  linarith [hlower, dist_comm ((g ^ a) • x) x,
    dist_comm ((h ^ b) • x) x]

/-- Geometric form of `acylindrical_common_power_pigeonhole`: sufficiently
many distinct exponent pairs whose two orbit maps fellow-travel at two distant
basepoints force a common nonzero power. -/
theorem acylindrical_common_power_of_two_orbit_fellow_travel
    (hiso : IsIsometricAction G X) (hacy : IsAcylindrical G X)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (R : ℝ) (N : ℕ), ∀ (x y : X), R ≤ dist x y →
      ∀ (g h : G) (a b : Fin (N + 1) → ℤ),
        Function.Injective a → Function.Injective b →
        (∀ i, dist ((g ^ (a i)) • x) ((h ^ (b i)) • x) ≤ ε ∧
          dist ((g ^ (a i)) • y) ((h ^ (b i)) • y) ≤ ε) →
        ∃ i j : Fin (N + 1), i ≠ j ∧
          a i - a j ≠ 0 ∧ b i - b j ≠ 0 ∧
          g ^ (a i - a j) = h ^ (b i - b j) := by
  obtain ⟨R, N, hRN⟩ := acylindrical_common_power_pigeonhole hacy hε
  refine ⟨R, N, fun x y hxy g h a b ha hb hclose => ?_⟩
  apply hRN x y hxy g h a b ha hb
  intro i
  rw [dist_zpow_difference hiso, dist_zpow_difference hiso]
  exact hclose i

/-! ## Loxodromics, independence, non-elementarity -/

/-- `S` acts non-elementarily at `x` when it contains two independent
loxodromics. -/
def ActsNonElementarily (S : Subgroup G) (x : X) : Prop :=
  ∃ g ∈ S, ∃ h ∈ S, IsLoxodromic g x ∧ IsLoxodromic h x ∧ Independent g h x

/-- Independence of two loxodromic directions does not depend on the chosen
basepoint.  Moving the two endpoints and the basepoint costs at most three
times the distance between the basepoints. -/
theorem independent_of_independent (hiso : IsIsometricAction G X) {g h : G}
    {x y : X} (hind : Independent g h x) : Independent g h y := by
  obtain ⟨C, hC⟩ := hind
  refine ⟨C + 3 * dist x y, ?_⟩
  intro n m
  have hgn : dist ((g ^ n) • y) ((g ^ n) • x) = dist y x :=
    hiso (g ^ n) y x
  have hhm : dist ((h ^ m) • y) ((h ^ m) • x) = dist y x :=
    hiso (h ^ m) y x
  calc
    gromovProduct ((g ^ n) • y) ((h ^ m) • y) y ≤
        gromovProduct ((g ^ n) • x) ((h ^ m) • y) y +
          dist ((g ^ n) • y) ((g ^ n) • x) :=
      gromovProduct_le_add_dist_left _ _ _ _
    _ ≤ gromovProduct ((g ^ n) • x) ((h ^ m) • x) y +
          dist ((g ^ n) • y) ((g ^ n) • x) +
          dist ((h ^ m) • y) ((h ^ m) • x) := by
      have hmove := gromovProduct_le_add_dist_right
        ((g ^ n) • x) ((h ^ m) • y) ((h ^ m) • x) y
      linarith
    _ ≤ gromovProduct ((g ^ n) • x) ((h ^ m) • x) x +
          dist y x + dist ((g ^ n) • y) ((g ^ n) • x) +
          dist ((h ^ m) • y) ((h ^ m) • x) := by
      have hmove := gromovProduct_le_add_dist_base
        ((g ^ n) • x) ((h ^ m) • x) y x
      linarith
    _ ≤ C + 3 * dist x y := by
      have hc := hC n m
      rw [hgn, hhm, dist_comm y x]
      linarith

/-- Independence is invariant under simultaneous conjugation. -/
theorem independent_conj (hiso : IsIsometricAction G X) {g h a : G} {x : X}
    (hind : Independent g h x) :
    Independent (a * g * a⁻¹) (a * h * a⁻¹) x := by
  obtain ⟨C, hC⟩ := independent_of_independent hiso hind (y := a⁻¹ • x)
  refine ⟨C, ?_⟩
  intro n m
  rw [conj_zpow, conj_zpow]
  calc
    gromovProduct ((a * g ^ n * a⁻¹) • x) ((a * h ^ m * a⁻¹) • x) x =
        gromovProduct (a • ((g ^ n) • (a⁻¹ • x)))
          (a • ((h ^ m) • (a⁻¹ • x))) (a • (a⁻¹ • x)) := by
      simp only [mul_smul, smul_inv_smul]
    _ = gromovProduct ((g ^ n) • (a⁻¹ • x))
          ((h ^ m) • (a⁻¹ • x)) (a⁻¹ • x) :=
      gromovProduct_smul hiso a _ _ _
    _ ≤ C := hC n m

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
  have hev := hg.isEscaping.eventually_ge_atTop (1 : ℝ)
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
  have hev := hh.isEscaping.eventually_ge_atTop (C + 1)
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
  have hev := hg.isEscaping.eventually_ge_atTop (C + 1)
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
  have hev := hg.isEscaping.eventually_ge_atTop (R + 2 * C)
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

`IsEscaping` above asks only that the power orbit escape every bounded set.
`IsLoxodromic` is the quantitative form needed by the geometry: the orbit map
is bounded below by a positive linear function up to additive error.  A
compression relation destroys this stronger property.

A compression `t p t⁻¹ = p ^ k` with `2 ≤ k` makes the orbit of `p` grow at most
*linearly in `j`* along the exponentially sparse subsequence `k ^ j`, because
`p ^ (k ^ j)` is a conjugate of `p` by `t ^ j` and conjugating by `t ^ j` costs
at most `j` displacements of `t`, twice.  A logarithmic orbit is not bounded
below by a linear one.

This is the first step of the route that would refute suitability for a
compression pattern outright: it settles the compressed direction, where the
Baumslag--Solitar relation lives.  It does not settle the defect, whose elements
are not powers of `p`. -/

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
theorem not_isLoxodromic_of_compression (hiso : IsIsometricAction G X)
    {t p : G} {k : ℕ} (hk : 2 ≤ k) (h : t * p * t⁻¹ = p ^ k) (x : X) :
    ¬ IsLoxodromic p x := by
  rintro ⟨l, hl, B, hB, hle⟩
  set D := dist x (t • x) with hD
  set E := dist x (p • x) with hE
  have hD0 : (0:ℝ) ≤ D := dist_nonneg
  have hE0 : (0:ℝ) ≤ E := dist_nonneg
  obtain ⟨j, hj⟩ := exists_nat_gt (max ((4 * D + E + B + 1) / l) 1)
  have hjr : (1:ℝ) < (j : ℝ) := lt_of_le_of_lt (le_max_right _ _) hj
  have hjd : (4 * D + E + B + 1) / l < (j : ℝ) :=
    lt_of_le_of_lt (le_max_left _ _) hj
  have hlj : 4 * D + E + B + 1 < (j : ℝ) * l :=
    (div_lt_iff₀ hl).mp hjd
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
  have hquad : 4 * (j : ℝ) * D + E + B < l * ((j : ℝ)) ^ 2 := by
    have hstep : (4 * D + E + B + 1) * (j : ℝ) <
        ((j : ℝ) * l) * (j : ℝ) :=
      mul_lt_mul_of_pos_right hlj (by linarith)
    nlinarith [hstep, hD0, hE0, hB, hjr]
  linarith

/-! ## Translation length

The first component of the machinery that would decide suitability outright.
`stableTranslation` is the infimum of `d(x, gⁿ x) / n` over positive `n` --- the
Fekete limit of the same sequence, but taken as an infimum so that no
subadditivity argument is needed for the two facts that matter here: it bounds
the orbit from below, and positivity implies genuine loxodromy.

Together with `not_isLoxodromic_of_compression` this reads: a compressed
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

theorem stableTranslation_le_dist_smul (g : G) (x : X) :
    stableTranslation g x ≤ dist x (g • x) := by
  simpa using stableTranslation_le g x (n := 1) Nat.one_pos

/-- The translation length bounds the orbit from below. -/
theorem mul_le_dist_pow (g : G) (x : X) (n : ℕ) :
    stableTranslation g x * n ≤ dist x ((g ^ n) • x) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn' : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn
    have h := stableTranslation_le g x hn
    rw [le_div_iff₀ hn'] at h
    exact h

/-- Positive stable translation length gives genuine loxodromy.  The converse
requires the subadditive-limit theorem below; it is deliberately not smuggled
in through the definition of `stableTranslation`. -/
theorem isLoxodromic_of_pos_stableTranslation (g : G) (x : X)
    (h : 0 < stableTranslation g x) : IsLoxodromic g x :=
  ⟨stableTranslation g x, h, 0, le_rfl, by simpa using mul_le_dist_pow g x⟩

/-- **A compressed element has translation length zero.** -/
theorem stableTranslation_eq_zero_of_compression (hiso : IsIsometricAction G X)
    {t p : G} {k : ℕ} (hk : 2 ≤ k) (h : t * p * t⁻¹ = p ^ k) (x : X) :
    stableTranslation p x = 0 := by
  by_contra hne
  refine not_isLoxodromic_of_compression hiso hk h x ?_
  exact isLoxodromic_of_pos_stableTranslation p x
    (lt_of_le_of_ne (stableTranslation_nonneg p x) (Ne.symm hne))

/-- Loxodromy does not depend on the basepoint. -/
theorem isLoxodromic_of_isLoxodromic (hiso : IsIsometricAction G X) {g : G}
    {x y : X} (h : IsLoxodromic g x) : IsLoxodromic g y := by
  obtain ⟨l, hl, B, hB, hlin⟩ := h
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
  refine ⟨l, hl, B + 2 * dist x y, by positivity, ?_⟩
  intro n
  exact le_trans (by linarith [hlin n]) (hbound n)

/-- Loxodromy is invariant under inversion. -/
theorem isLoxodromic_inv (hiso : IsIsometricAction G X) {g : G} {x : X}
    (hg : IsLoxodromic g x) : IsLoxodromic g⁻¹ x := by
  obtain ⟨l, hl, B, hB, hlin⟩ := hg
  have hdist : ∀ n : ℕ,
      dist x (((g⁻¹) ^ n) • x) = dist x ((g ^ n) • x) := by
    intro n
    have h := dist_zpow_neg (g := g) (x := x) hiso (n : ℤ)
    simpa only [zpow_neg, zpow_natCast, inv_pow] using h
  exact ⟨l, hl, B, hB, fun n => by rw [hdist]; exact hlin n⟩

/-- Every positive power of a loxodromic element is loxodromic. -/
theorem isLoxodromic_pow {g : G} {x : X} (hg : IsLoxodromic g x)
    {k : ℕ} (hk : 0 < k) :
    IsLoxodromic (g ^ k) x := by
  obtain ⟨l, hl, B, hB, hlin⟩ := hg
  refine ⟨l * k, by positivity, B, hB, ?_⟩
  intro n
  rw [← pow_mul]
  have h := hlin (k * n)
  push_cast at h ⊢
  nlinarith

/-- Every nonzero integer power of a loxodromic element is loxodromic. -/
theorem isLoxodromic_zpow (hiso : IsIsometricAction G X) {g : G} {x : X}
    (hg : IsLoxodromic g x) {k : ℤ} (hk : k ≠ 0) :
    IsLoxodromic (g ^ k) x := by
  cases k with
  | ofNat n =>
      have hn : 0 < n := Nat.pos_of_ne_zero (by
        intro hn
        apply hk
        simp [hn])
      have hp : IsLoxodromic (g ^ n) x :=
        isLoxodromic_pow (g := g) hg hn
      change IsLoxodromic (g ^ (n : ℤ)) x
      simpa only [zpow_natCast] using hp
  | negSucc n =>
      have hp : IsLoxodromic (g ^ (n + 1)) x :=
        isLoxodromic_pow hg (Nat.succ_pos n)
      have hi := isLoxodromic_inv hiso hp
      simpa only [zpow_negSucc] using hi

/-- Loxodromy descends from a positive power to the element itself.  Between
two consecutive multiples of `k`, the orbit loses at most `k` one-step
displacements, so the linear lower bound on the subsequence extends to the
whole orbit with a larger additive constant. -/
theorem isLoxodromic_of_pow_isLoxodromic (hiso : IsIsometricAction G X)
    {g : G} {x : X} {k : ℕ} (hk : 0 < k)
    (hgk : IsLoxodromic (g ^ k) x) : IsLoxodromic g x := by
  obtain ⟨l, hl, B, hB, hlin⟩ := hgk
  let D : ℝ := dist x (g • x)
  have hD : 0 ≤ D := dist_nonneg
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  refine ⟨l / k, div_pos hl hkR, B + l + k * D, by positivity, ?_⟩
  intro n
  let q : ℕ := n / k
  let r : ℕ := n % k
  have hr : r < k := Nat.mod_lt n hk
  have hn : n = k * q + r := by
    calc
      n = k * (n / k) + n % k := (Nat.div_add_mod n k).symm
      _ = k * q + r := by rfl
  have hstep :
      dist ((g ^ (k * q)) • x) ((g ^ n) • x) = dist x ((g ^ r) • x) := by
    rw [hn, pow_add, mul_smul, hiso (g ^ (k * q)) x ((g ^ r) • x)]
  have hrem : dist x ((g ^ r) • x) ≤ k * D := by
    have hu := dist_pow_le hiso g x r
    have hrle : (r : ℝ) ≤ k := by exact_mod_cast (Nat.le_of_lt hr)
    dsimp [D]
    exact le_trans hu (mul_le_mul_of_nonneg_right hrle dist_nonneg)
  have hsubseq : l * q - B ≤ dist x ((g ^ (k * q)) • x) := by
    have hq := hlin q
    simpa only [pow_mul] using hq
  have htri := dist_triangle x ((g ^ n) • x) ((g ^ (k * q)) • x)
  rw [dist_comm ((g ^ n) • x) ((g ^ (k * q)) • x), hstep] at htri
  have hnle : (n : ℝ) ≤ (k : ℝ) * (q : ℝ) + k := by
    exact_mod_cast (show n ≤ k * q + k by omega)
  have hslope : (l / k) * n ≤ l * q + l := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hkR]
    nlinarith
  dsimp [D]
  linarith

/-- Loxodromy descends from every nonzero integer power. -/
theorem isLoxodromic_of_zpow_isLoxodromic (hiso : IsIsometricAction G X)
    {g : G} {x : X} {k : ℤ} (hk : k ≠ 0)
    (hgk : IsLoxodromic (g ^ k) x) : IsLoxodromic g x := by
  cases k with
  | ofNat n =>
      have hn : 0 < n := Nat.pos_of_ne_zero (by simpa using hk)
      have hgk' : IsLoxodromic (g ^ n) x := by
        change IsLoxodromic (g ^ (n : ℤ)) x at hgk
        simpa only [zpow_natCast] using hgk
      exact isLoxodromic_of_pow_isLoxodromic hiso hn hgk'
  | negSucc n =>
      have hinv : IsLoxodromic (g ^ (n + 1)) x := by
        have := isLoxodromic_inv hiso hgk
        simpa only [zpow_negSucc, inv_inv] using this
      exact isLoxodromic_of_pow_isLoxodromic hiso (Nat.succ_pos n) hinv

/-- A nonzero common-power equation transfers loxodromy in either direction. -/
theorem isLoxodromic_of_common_zpow (hiso : IsIsometricAction G X)
    {g h : G} {x : X} (hg : IsLoxodromic g x) {a b : ℤ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hp : g ^ a = h ^ b) :
    IsLoxodromic h x := by
  have hga : IsLoxodromic (g ^ a) x := isLoxodromic_zpow hiso hg ha
  have hhb : IsLoxodromic (h ^ b) x := by simpa only [hp] using hga
  exact isLoxodromic_of_zpow_isLoxodromic hiso hb hhb

/-- Loxodromy is invariant under conjugation.  The orbit of `a * g * a⁻¹`
based at `x` is isometric to the orbit of `g` based at `a⁻¹ • x`; basepoint
independence supplies loxodromy at that latter point. -/
theorem isLoxodromic_conj (hiso : IsIsometricAction G X) {g a : G} {x : X}
    (hg : IsLoxodromic g x) : IsLoxodromic (a * g * a⁻¹) x := by
  have hgbase : IsLoxodromic g (a⁻¹ • x) :=
    isLoxodromic_of_isLoxodromic hiso hg
  have hpow : ∀ n : ℕ, (a * g * a⁻¹) ^ n = a * g ^ n * a⁻¹ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ, ih]
        group
  have hdist : ∀ n : ℕ,
      dist x (((a * g * a⁻¹) ^ n) • x) =
        dist (a⁻¹ • x) ((g ^ n) • (a⁻¹ • x)) := by
    intro n
    have h := hiso a (a⁻¹ • x) ((g ^ n) • (a⁻¹ • x))
    rw [hpow]
    simpa only [← mul_smul, mul_inv_cancel, one_smul, mul_assoc] using h
  obtain ⟨l, hl, B, hB, hlin⟩ := hgbase
  exact ⟨l, hl, B, hB, fun n => by rw [hdist]; exact hlin n⟩

/-- A normal subgroup acts non-elementarily as soon as one of its loxodromic
elements has an independent conjugate.  Normality puts the conjugate back in
the subgroup, and `isLoxodromic_conj` supplies its loxodromy.  This isolates the
remaining geometric heart of Osin's s-normal argument: producing the
independent conjugator. -/
theorem actsNonElementarily_of_normal_conjugate {S : Subgroup G} [S.Normal]
    (hiso : IsIsometricAction G X) {g a : G} {x : X} (hgS : g ∈ S)
    (hg : IsLoxodromic g x) (hind : Independent g (a * g * a⁻¹) x) :
    ActsNonElementarily S x := by
  refine ⟨g, hgS, a * g * a⁻¹, ?_, hg, isLoxodromic_conj hiso hg, hind⟩
  exact (inferInstance : S.Normal).conj_mem g hgS a

/-- **Independent conjugate axes give a loxodromic commutator in a normal
subgroup.**

If `c ∈ S` and the axes of `g` and `c g⁻¹ c⁻¹` are independent, the
independent-axes ping-pong theorem produces a loxodromic

`gᴺ (c g⁻¹ c⁻¹)ᴺ = gᴺ c g⁻ᴺ c⁻¹`.

The latter is a commutator and lies in the normal subgroup `S`.  This is the
complete independent branch of the normal-subgroup loxodromic-extraction
argument. -/
theorem exists_loxodromic_commutator_of_independent_conjugate
    {δ : ℝ} (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ)
    (hiso : IsIsometricAction G X) {S : Subgroup G} [S.Normal]
    {g c : G} {x : X} (hcS : c ∈ S) (hg : IsLoxodromic g x)
    (hind : Independent g (c * g⁻¹ * c⁻¹) x) :
    ∃ N : ℕ, g ^ N * c * (g ^ N)⁻¹ * c⁻¹ ∈ S ∧
      IsLoxodromic (g ^ N * c * (g ^ N)⁻¹ * c⁻¹) x := by
  have hginv : IsLoxodromic g⁻¹ x := isLoxodromic_inv hiso hg
  have hb : IsLoxodromic (c * g⁻¹ * c⁻¹) x :=
    isLoxodromic_conj hiso hginv
  obtain ⟨N, hN⟩ := exists_isLoxodromic_mul_pow_of_independent
    hδ hδ0 hiso hg hb hind
  have hpow : (c * g⁻¹ * c⁻¹) ^ N = c * (g ^ N)⁻¹ * c⁻¹ := by
    rw [conj_pow, inv_pow]
  refine ⟨N, ?_, ?_⟩
  · exact S.mul_mem ((inferInstance : S.Normal).conj_mem c hcS (g ^ N))
      (S.inv_mem hcS)
  · have heq : g ^ N * (c * g⁻¹ * c⁻¹) ^ N =
        g ^ N * c * (g ^ N)⁻¹ * c⁻¹ := by
      rw [hpow]
      group
    rw [← heq]
    exact hN

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

/-- The additive-error definition of genuine loxodromy forces positive stable
translation.  Divide its lower bound by `n`; after `n` is large enough to
absorb the additive constant, every normalised displacement is at least
`l / 2`, and the Fekete limit preserves that lower bound. -/
theorem stableTranslation_pos_of_isLoxodromic
    (hiso : IsIsometricAction G X) {g : G} {x : X}
    (hg : IsLoxodromic g x) : 0 < stableTranslation g x := by
  obtain ⟨l, hl, B, hB, hlin⟩ := hg
  have hev : ∀ᶠ n : ℕ in Filter.atTop,
      l / 2 ≤ dist x ((g ^ n) • x) / n := by
    obtain ⟨N, hN⟩ := exists_nat_gt (max (2 * B / l) 0)
    rw [Filter.eventually_atTop]
    refine ⟨N, fun n hn => ?_⟩
    have hn0 : 0 < n := by
      have hNR : (0 : ℝ) < N := lt_of_le_of_lt (le_max_right _ _) hN
      have hN0 : 0 < N := by exact_mod_cast hNR
      exact lt_of_lt_of_le hN0 hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
    rw [le_div_iff₀ hnR]
    have hncast : (N : ℝ) ≤ n := by exact_mod_cast hn
    have hlarge : 2 * B / l < (n : ℝ) :=
      lt_of_le_of_lt (le_max_left _ _) (lt_of_lt_of_le hN hncast)
    have hBn : 2 * B < l * (n : ℝ) := by
      rw [div_lt_iff₀ hl] at hlarge
      linarith
    have hlower := hlin n
    linarith
  have hlimit : l / 2 ≤ stableTranslation g x :=
    ge_of_tendsto (tendsto_stableTranslation hiso g x) hev
  linarith

/-- Genuine loxodromy is equivalent to positive stable translation length. -/
theorem isLoxodromic_iff_stableTranslation_pos
    (hiso : IsIsometricAction G X) (g : G) (x : X) :
    IsLoxodromic g x ↔ 0 < stableTranslation g x :=
  ⟨stableTranslation_pos_of_isLoxodromic hiso,
    isLoxodromic_of_pos_stableTranslation g x⟩

/-- A sufficiently large power of a loxodromic element has one-step
displacement more than twice its single-turn backtracking (with the
hyperbolicity allowance).  This follows from convergence of normalised
displacements: `d(x,gᵏx)/k` and `d(x,g²ᵏx)/(2k)` have the same positive limit,
so `d(x,g²ᵏx) - d(x,gᵏx)` grows linearly. -/
theorem exists_power_local_backtracking_gap
    (hiso : IsIsometricAction G X) {δ : ℝ} (_hδ0 : 0 ≤ δ)
    {g : G} {x : X} (hg : IsLoxodromic g x) :
    ∃ k : ℕ, 0 < k ∧
      2 * (gromovProduct x ((g ^ (2 * k)) • x) ((g ^ k) • x) + δ) <
        dist x ((g ^ k) • x) := by
  let τ : ℝ := stableTranslation g x
  have hτ : 0 < τ := stableTranslation_pos_of_isLoxodromic hiso hg
  have ht := tendsto_stableTranslation hiso g x
  have hup : ∀ᶠ n : ℕ in Filter.atTop,
      dist x ((g ^ n) • x) / n < 5 * τ / 4 :=
    ht.eventually_lt_const (by dsimp [τ]; linarith)
  have hlo : ∀ᶠ n : ℕ in Filter.atTop,
      3 * τ / 4 < dist x ((g ^ n) • x) / n :=
    ht.eventually_const_lt (by dsimp [τ]; linarith)
  rw [Filter.eventually_atTop] at hup hlo
  obtain ⟨Mu, hMu⟩ := hup
  obtain ⟨Ml, hMl⟩ := hlo
  obtain ⟨k, hklarge⟩ := exists_nat_gt
    (max (max (Mu : ℝ) Ml) (max (8 * δ / τ) 0))
  have hkMu : Mu ≤ k := by
    have hkMuR : (Mu : ℝ) ≤ k := le_trans (le_max_left (Mu : ℝ) Ml)
      (le_trans (le_max_left _ _) (le_of_lt hklarge))
    exact_mod_cast hkMuR
  have hkMl : Ml ≤ 2 * k := by
    have hMlk : (Ml : ℝ) ≤ k :=
      le_trans (le_max_right (Mu : ℝ) Ml)
        (le_trans (le_max_left _ _) (le_of_lt hklarge))
    have hk2k : (k : ℝ) ≤ 2 * k := by
      have hk_nonneg : (0 : ℝ) ≤ k := by positivity
      linarith
    exact_mod_cast le_trans hMlk hk2k
  have hk0 : 0 < k := by
    have hkR : (0 : ℝ) < k :=
      lt_of_le_of_lt (le_max_right (8 * δ / τ) 0)
        (lt_of_le_of_lt (le_max_right _ _) hklarge)
    exact_mod_cast hkR
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
  have h2k0 : 0 < 2 * k := by positivity
  have h2kR : (0 : ℝ) < ((2 * k : ℕ) : ℝ) := by exact_mod_cast h2k0
  have hu := hMu k hkMu
  have hl := hMl (2 * k) hkMl
  rw [div_lt_iff₀ hkR] at hu
  have hl' : 3 * τ / 4 * ((2 * k : ℕ) : ℝ) <
      dist x ((g ^ (2 * k)) • x) := (lt_div_iff₀ h2kR).mp hl
  push_cast at hl'
  have hkδ : 8 * δ / τ < (k : ℝ) :=
    lt_of_le_of_lt (le_max_left _ _) (lt_of_le_of_lt (le_max_right _ _) hklarge)
  have hδgrow : 2 * δ < τ * (k : ℝ) / 4 := by
    rw [div_lt_iff₀ hτ] at hkδ
    nlinarith
  have hgapdist :
      dist x ((g ^ k) • x) + 2 * δ < dist x ((g ^ (2 * k)) • x) := by
    nlinarith
  have hturn : gromovProduct x ((g ^ (2 * k)) • x) ((g ^ k) • x) =
      dist x ((g ^ k) • x) - dist x ((g ^ (2 * k)) • x) / 2 := by
    have hstep : dist ((g ^ (2 * k)) • x) ((g ^ k) • x) =
        dist x ((g ^ k) • x) := by
      have hz := hiso (g ^ k) x ((g ^ k) • x)
      have he : g ^ k * g ^ k = g ^ (2 * k) := by
        rw [← pow_add]
        congr 1
        omega
      rw [← mul_smul, he] at hz
      rw [dist_comm ((g ^ (2 * k)) • x) ((g ^ k) • x)]
      exact hz
    unfold gromovProduct
    rw [hstep]
    ring
  refine ⟨k, hk0, ?_⟩
  rw [hturn]
  linarith

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
needs is one.  For a loxodromic element the orbit map `k ↦ gᵏ x` is a
quasi-isometric embedding of the integers.  Its lower bound comes directly
from `IsLoxodromic`, including its additive error, and its upper bound is
`dist_pow_le`.  Passing from `ℕ` to `ℤ` uses `dist_zpow_neg`.

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

/-- Genuine loxodromy gives the full two-sided quasi-isometric orbit estimate
on the integers, with the same additive error as in the definition.  This is
the precise orbit input required by a Morse-stability theorem. -/
theorem orbit_quasiIsometricEmbedding_of_isLoxodromic
    (hiso : IsIsometricAction G X) {g : G} {x : X}
    (hg : IsLoxodromic g x) :
    ∃ l : ℝ, 0 < l ∧ ∃ B : ℝ, 0 ≤ B ∧ ∀ m n : ℤ,
      l * |((n - m : ℤ) : ℝ)| - B ≤
          dist ((g ^ m) • x) ((g ^ n) • x) ∧
        dist ((g ^ m) • x) ((g ^ n) • x) ≤
          |((n - m : ℤ) : ℝ)| * dist x (g • x) := by
  obtain ⟨l, hl, B, hB, hlin⟩ := hg
  refine ⟨l, hl, B, hB, fun m n => ?_⟩
  rw [dist_zpow_orbit hiso]
  constructor
  · rw [dist_zpow_natAbs hiso]
    have hcast : (((n - m).natAbs : ℕ) : ℝ) = |((n - m : ℤ) : ℝ)| := by
      rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
    simpa only [hcast] using hlin (n - m).natAbs
  · exact dist_zpow_le hiso g x (n - m)

/-- **The quasi-axis.**  The orbit map of a group element is a
quasi-isometric embedding of the integers, with lower constant its translation
length and upper constant its displacement.  When the translation length is
positive both bounds are effective.  For the more general additive-error
definition of loxodromy, use
`orbit_quasiIsometricEmbedding_of_isLoxodromic` above. -/
theorem orbit_quasiIsometricEmbedding (hiso : IsIsometricAction G X) (g : G)
    (x : X) (m n : ℤ) :
    stableTranslation g x * |((n - m : ℤ) : ℝ)|
        ≤ dist ((g ^ m) • x) ((g ^ n) • x) ∧
      dist ((g ^ m) • x) ((g ^ n) • x)
        ≤ |((n - m : ℤ) : ℝ)| * dist x (g • x) := by
  rw [dist_zpow_orbit hiso]
  exact ⟨mul_le_dist_zpow hiso g x (n - m), dist_zpow_le hiso g x (n - m)⟩

/-- A genuinely loxodromic orbit is bi-Lipschitz on the integers, with no
additive error: the lower constant is its positive stable translation and the
upper constant is its one-step displacement. -/
theorem exists_pos_orbit_biLipschitz (hiso : IsIsometricAction G X)
    {g : G} {x : X} (hg : IsLoxodromic g x) :
    ∃ l : ℝ, 0 < l ∧ ∀ m n : ℤ,
      l * |((n - m : ℤ) : ℝ)| ≤
          dist ((g ^ m) • x) ((g ^ n) • x) ∧
        dist ((g ^ m) • x) ((g ^ n) • x) ≤
          |((n - m : ℤ) : ℝ)| * dist x (g • x) := by
  refine ⟨stableTranslation g x,
    stableTranslation_pos_of_isLoxodromic hiso hg, ?_⟩
  exact orbit_quasiIsometricEmbedding hiso g x

/-- The basic quantitative excursion estimate for a loxodromic orbit.  A
Gromov product based at an orbit point is bounded by the difference between
the two upper Lipschitz legs and the stable-translation lower bound on the
opposite side.  This is the numerical inequality iterated in the dyadic proof
of Morse stability. -/
theorem two_mul_gromovProduct_zpow_le
    (hiso : IsIsometricAction G X) (g : G) (x : X) (i j k : ℤ) :
    2 * gromovProduct ((g ^ i) • x) ((g ^ k) • x) ((g ^ j) • x) ≤
      |((j - i : ℤ) : ℝ)| * dist x (g • x) +
        |((k - j : ℤ) : ℝ)| * dist x (g • x) -
          stableTranslation g x * |((k - i : ℤ) : ℝ)| := by
  have hleft := (orbit_quasiIsometricEmbedding hiso g x i j).2
  have hright := (orbit_quasiIsometricEmbedding hiso g x j k).2
  have hopposite := (orbit_quasiIsometricEmbedding hiso g x i k).1
  unfold gromovProduct
  rw [dist_comm ((g ^ k) • x) ((g ^ j) • x)]
  linarith

/-- Ordered form of the excursion estimate.  Along an interval of integer
orbit parameters, the two leg lengths add to the total parameter length. -/
theorem two_mul_gromovProduct_zpow_le_of_le
    (hiso : IsIsometricAction G X) (g : G) (x : X)
    {i j k : ℤ} (hij : i ≤ j) (hjk : j ≤ k) :
    2 * gromovProduct ((g ^ i) • x) ((g ^ k) • x) ((g ^ j) • x) ≤
      (dist x (g • x) - stableTranslation g x) * ((k - i : ℤ) : ℝ) := by
  have h := two_mul_gromovProduct_zpow_le hiso g x i j k
  rw [abs_of_nonneg (by exact_mod_cast sub_nonneg.mpr hij),
    abs_of_nonneg (by exact_mod_cast sub_nonneg.mpr hjk),
    abs_of_nonneg (by exact_mod_cast sub_nonneg.mpr (le_trans hij hjk))] at h
  push_cast at h ⊢
  nlinarith

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

/-- **Local bounded backtracking gives uniform global backtracking and linear
progress.**

Suppose every edge of a chain has length at least `L`, and at each intermediate
vertex the Gromov product of the preceding and following vertices is at most
`C`.  If `L > 2(C + δ)`, the four-point inequality propagates the local bound:
the Gromov product of the initial vertex and the next vertex, based at the
current vertex, is always at most `C + δ`.  Consequently every edge advances
the distance from the initial vertex by at least `L - 2(C + δ)`.

This is the concrete local-to-global estimate needed for ping-pong products;
unlike the earlier linear-loss chain inequality, its loss is uniform. -/
theorem chain_backtracking_and_progress {δ C L : ℝ}
    (hδ : IsHyperbolicSpace δ X) (hCδ : 0 ≤ C + δ)
    (hgap : 2 * (C + δ) < L) (y : ℕ → X)
    (hedge : ∀ n : ℕ, L ≤ dist (y n) (y (n + 1)))
    (hlocal : ∀ n : ℕ,
      gromovProduct (y n) (y (n + 2)) (y (n + 1)) ≤ C) :
    ∀ n : ℕ,
      (L - 2 * (C + δ)) * n ≤ dist (y 0) (y n) ∧
        gromovProduct (y 0) (y (n + 1)) (y n) ≤ C + δ := by
  intro n
  induction n with
  | zero =>
      constructor
      · simp
      · have hzero : gromovProduct (y 0) (y 1) (y 0) = 0 := by
          unfold gromovProduct
          rw [dist_self, dist_comm (y 1) (y 0)]
          ring
        rw [hzero]
        exact hCδ
  | succ n ih =>
      have hed := hedge n
      have hdist :
          dist (y 0) (y n) + L - 2 * (C + δ) ≤
            dist (y 0) (y (n + 1)) := by
        have hb := ih.2
        unfold gromovProduct at hb
        rw [dist_comm (y (n + 1)) (y n)] at hb
        linarith
      constructor
      · have hp := ih.1
        push_cast
        linarith
      · have hswap := gromovProduct_add_swap_base (y 0) (y n) (y (n + 1))
        have hbehind : C + δ <
            gromovProduct (y 0) (y n) (y (n + 1)) := by
          linarith [ih.2, hedge n]
        have hloc := hlocal n
        have hfar :
            gromovProduct (y n) (y (n + 2)) (y (n + 1)) + δ <
              gromovProduct (y 0) (y n) (y (n + 1)) := by
          linarith
        have hnext := gromovProduct_le_add_delta_of_lt hδ hfar
        have hbound :
            gromovProduct (y 0) (y (n + 2)) (y (n + 1)) ≤ C + δ := by
          linarith
        simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using hbound

/-- **One local turn certifies a loxodromic orbit.**

For a group orbit all edges have the same length and all local turns are
isometric translates of the turn at `p x`.  Hence the preceding chain theorem
reduces the entire local-to-global problem to the single inequality

`(x | p²x)_{p x} ≤ C`

together with `2(C + δ) < d(x, p x)`. -/
theorem isLoxodromic_of_local_backtracking {δ C : ℝ}
    (hδ : IsHyperbolicSpace δ X) (hiso : IsIsometricAction G X)
    {p : G} {x : X} (hCδ : 0 ≤ C + δ)
    (hgap : 2 * (C + δ) < dist x (p • x))
    (hturn : gromovProduct x ((p ^ 2) • x) (p • x) ≤ C) :
    IsLoxodromic p x := by
  let y : ℕ → X := fun n => (p ^ n) • x
  have hedge : ∀ n : ℕ,
      dist x (p • x) ≤ dist (y n) (y (n + 1)) := by
    intro n
    have h := hiso (p ^ n) x (p • x)
    rw [← mul_smul, ← pow_succ] at h
    exact le_of_eq h.symm
  have hlocal : ∀ n : ℕ,
      gromovProduct (y n) (y (n + 2)) (y (n + 1)) ≤ C := by
    intro n
    have h := gromovProduct_smul hiso (p ^ n) x ((p ^ 2) • x) (p • x)
    have htwo : p ^ n * p ^ 2 = p ^ (n + 2) := by rw [← pow_add]
    have hone : p ^ n * p = p ^ (n + 1) := by rw [← pow_succ]
    rw [← mul_smul, htwo, ← mul_smul, hone] at h
    change gromovProduct (y n) (y (n + 2)) (y (n + 1)) =
      gromovProduct x ((p ^ 2) • x) (p • x) at h
    exact h.trans_le hturn
  have hall := chain_backtracking_and_progress hδ hCδ hgap y hedge hlocal
  refine ⟨dist x (p • x) - 2 * (C + δ), by linarith, 0, le_rfl, ?_⟩
  intro n
  simpa [y] using (hall n).1

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

/-- Move the basepoint of an orbit-backtracking product back to `x`.

The `n`-th term in the bounded-backtracking criterion is exactly the Gromov
product between the negative orbit point `p⁻ⁿx` and the one-step positive point
`p x`, based at `x`.  Thus the apparently moving-basepoint condition is a
fixed-basepoint separation estimate between the two orbit directions. -/
theorem gromovProduct_orbit_backtracking_eq (hiso : IsIsometricAction G X)
    (p : G) (x : X) (n : ℤ) :
    gromovProduct x ((p ^ (n + 1)) • x) ((p ^ n) • x) =
      gromovProduct ((p ^ (-n)) • x) (p • x) x := by
  have hnext : p ^ (-n) * p ^ (n + 1) = p := by
    rw [← zpow_add]
    simp
  have hbase : p ^ (-n) * p ^ n = 1 := by
    rw [← zpow_add]
    simp
  calc
    gromovProduct x ((p ^ (n + 1)) • x) ((p ^ n) • x) =
        gromovProduct ((p ^ (-n)) • x)
          ((p ^ (-n)) • ((p ^ (n + 1)) • x))
          ((p ^ (-n)) • ((p ^ n) • x)) :=
      (gromovProduct_smul hiso (p ^ (-n)) x
        ((p ^ (n + 1)) • x) ((p ^ n) • x)).symm
    _ = gromovProduct ((p ^ (-n)) • x) (p • x) x := by
      rw [← mul_smul, hnext, ← mul_smul, hbase, one_smul]

/-- The natural-power form consumed directly by
`isLoxodromic_of_bounded_orbit_backtracking`. -/
theorem gromovProduct_orbit_backtracking_eq_nat
    (hiso : IsIsometricAction G X) (p : G) (x : X) (n : ℕ) :
    gromovProduct x ((p ^ (n + 1)) • x) ((p ^ n) • x) =
      gromovProduct ((p ^ (-(n : ℤ))) • x) (p • x) x := by
  have h := gromovProduct_orbit_backtracking_eq hiso p x (n : ℤ)
  have he : (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) := by omega
  rw [he, zpow_natCast, zpow_natCast] at h
  exact h

/-- Multiplying a long loxodromic power by a fixed element loses at most the
fixed element's displacement.  This is the elementary displacement half of the
standard `gⁿ c` loxodromic-product argument. -/
theorem dist_pow_mul_lower (hiso : IsIsometricAction G X) (g c : G) (x : X)
    (n : ℕ) :
    dist x ((g ^ n) • x) - dist x (c • x) ≤
      dist x (((g ^ n) * c) • x) := by
  have htri := dist_triangle x (((g ^ n) * c) • x) ((g ^ n) • x)
  have htail :
      dist (((g ^ n) * c) • x) ((g ^ n) • x) = dist (c • x) x := by
    have h := hiso (g ^ n) (c • x) x
    rw [← mul_smul] at h
    exact h
  rw [htail, dist_comm (c • x) x] at htri
  linarith

/-- A sufficiently long power in `gⁿ c` makes its one-step displacement exceed
any prescribed backtracking budget.  Thus, for the bounded-backtracking
criterion below, the positivity inequality is automatic; only the uniform
Gromov-product estimate remains. -/
theorem exists_pow_mul_progress (hiso : IsIsometricAction G X)
    {g : G} (c : G) {x : X} (hg : IsLoxodromic g x) (A : ℝ) :
    ∃ n : ℕ, 2 * A < dist x (((g ^ n) * c) • x) := by
  have hev := hg.isEscaping.eventually_ge_atTop
    (2 * A + dist x (c • x) + 1)
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  refine ⟨N, ?_⟩
  have hlarge := hN N le_rfl
  have hlower := dist_pow_mul_lower hiso g c x N
  linarith

/-- **Bounded backtracking makes an element genuinely loxodromic.**

Let `D = d(x, p x)`.  At the `n`-th orbit point, the Gromov product

`(x | pⁿ⁺¹x)_{pⁿx}`

measures exactly half the amount by which the next step fails to add its full
length `D` to the distance from `x`.  Consequently, if all these products are
at most `A` and `2A < D`, every step makes progress at least `D - 2A`, and

`d(x, pⁿx) ≥ n (D - 2A)`.

This is the quantitative last step in a loxodromic-product argument.  For a
candidate such as `p = g ^ m * c`, the remaining ping-pong task is now the
concrete inequality `hback` rather than an unnamed local-to-global premise. -/
theorem isLoxodromic_of_bounded_orbit_backtracking
    (hiso : IsIsometricAction G X) {p : G} {x : X} {A : ℝ}
    (hprogress : 2 * A < dist x (p • x))
    (hback : ∀ n : ℕ,
      gromovProduct x ((p ^ (n + 1)) • x) ((p ^ n) • x) ≤ A) :
    IsLoxodromic p x := by
  let l : ℝ := dist x (p • x) - 2 * A
  have hl : 0 < l := by
    dsimp [l]
    linarith
  have hlower : ∀ n : ℕ, l * n ≤ dist x ((p ^ n) • x) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have hstep :
            dist ((p ^ n) • x) ((p ^ (n + 1)) • x) = dist x (p • x) := by
          have h := hiso (p ^ n) x (p • x)
          rw [← mul_smul, ← pow_succ] at h
          exact h
        have hb := hback n
        rw [gromovProduct,
          dist_comm ((p ^ (n + 1)) • x) ((p ^ n) • x), hstep] at hb
        push_cast
        dsimp [l] at ih ⊢
        linarith
  exact ⟨l, hl, 0, le_rfl, by simpa using hlower⟩

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

/-- A Gromov product is at most the distance from either of its entries to
the basepoint.  This elementary bound is what permits a finite chain to be
padded by repetitions of its final vertex. -/
theorem gromovProduct_le_right (x y w : X) :
    gromovProduct x y w ≤ dist y w := by
  have htri : dist x w ≤ dist x y + dist y w := dist_triangle x y w
  unfold gromovProduct
  linarith

/-- **The logarithmic chain estimate for an arbitrary finite chain.**

If a chain has `N ≤ 2 ^ k` edges, pad it to `2 ^ k` edges by repeating its
last vertex.  The genuine edges have the assumed lower Gromov-product bound;
the padded edges have Gromov product `dist (y N) w`.  Thus the dyadic chain
lemma applies with the same `k · δ` loss.

The endpoint-distance hypothesis is separated out because this form is useful
also for a chain with no edges.  The positive-length corollary below derives it
from the final genuine edge. -/
theorem gromovProduct_chain_le_pow_two {δ : ℝ}
    (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ) (w : X) (y : ℕ → X)
    (c : ℝ) (N k : ℕ) (hN : N ≤ 2 ^ k)
    (hc : ∀ i, i < N → c ≤ gromovProduct (y i) (y (i + 1)) w)
    (hend : c ≤ dist (y N) w) :
    c - k * δ ≤ gromovProduct (y 0) (y N) w := by
  let z : ℕ → X := fun i => y (Nat.min i N)
  have hz : ∀ i, i < 2 ^ k → c ≤ gromovProduct (z i) (z (i + 1)) w := by
    intro i hi
    by_cases hiN : i < N
    · have hi_le : i ≤ N := Nat.le_of_lt hiN
      have his_le : i + 1 ≤ N := by omega
      simpa [z, Nat.min_eq_left hi_le, Nat.min_eq_left his_le] using hc i hiN
    · have hNi : N ≤ i := Nat.le_of_not_gt hiN
      have hNis : N ≤ i + 1 := le_trans hNi (Nat.le_succ i)
      simpa [z, Nat.min_eq_right hNi, Nat.min_eq_right hNis,
        gromovProduct_self] using hend
  have h := gromovProduct_chain_pow_two hδ hδ0 w c k z hz
  simpa [z, Nat.min_eq_right hN] using h

/-- For a nonempty chain the endpoint-distance condition needed for padding is
automatic: the Gromov product on its final edge is bounded above by the
distance from the final vertex to the basepoint. -/
theorem gromovProduct_chain_le_pow_two_of_pos {δ : ℝ}
    (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ) (w : X) (y : ℕ → X)
    (c : ℝ) (N k : ℕ) (hNpos : 0 < N) (hN : N ≤ 2 ^ k)
    (hc : ∀ i, i < N → c ≤ gromovProduct (y i) (y (i + 1)) w) :
    c - k * δ ≤ gromovProduct (y 0) (y N) w := by
  have hlast := hc (N - 1) (Nat.sub_lt hNpos Nat.one_pos)
  have hsucc : N - 1 + 1 = N := Nat.sub_add_cancel hNpos
  have hend : c ≤ dist (y N) w := by
    rw [hsucc] at hlast
    exact le_trans hlast (gromovProduct_le_right _ _ _)
  exact gromovProduct_chain_le_pow_two hδ hδ0 w y c N k hN hc hend

/-- **Discrete exponential divergence.**  Let a chain of `N` edges, each of
length at most `D`, stay outside the radius-`R` ball about `w`.  Consecutive
vertices then have Gromov product at least `R - D/2` at `w`.  If
`N ≤ 2ᵏ`, the dyadic chain lemma forces the endpoints' Gromov product to be
at least `R - D/2 - kδ`.

Equivalently, when the endpoint product is at most `C`, one has
`R ≤ C + D/2 + kδ`.  This is the exponential-detour estimate at the heart of
the Morse excursion argument, proved directly from four-point hyperbolicity. -/
theorem radius_le_of_chain_avoids_ball {δ D R C : ℝ}
    (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ) (w : X) (y : ℕ → X)
    (N k : ℕ) (hNpos : 0 < N) (hN : N ≤ 2 ^ k)
    (hedge : ∀ i, i < N → dist (y i) (y (i + 1)) ≤ D)
    (havoid : ∀ i, i ≤ N → R ≤ dist (y i) w)
    (hend : gromovProduct (y 0) (y N) w ≤ C) :
    R ≤ C + D / 2 + k * δ := by
  have hlocal : ∀ i, i < N →
      R - D / 2 ≤ gromovProduct (y i) (y (i + 1)) w := by
    intro i hi
    have hiN : i ≤ N := by omega
    have hisN : i + 1 ≤ N := by omega
    have hleft := havoid i hiN
    have hright := havoid (i + 1) hisN
    have he := hedge i hi
    unfold gromovProduct
    linarith
  have hchain := gromovProduct_chain_le_pow_two_of_pos hδ hδ0 w y
    (R - D / 2) N k hNpos hN hlocal
  linarith

/-- Canonical logarithmic form of discrete divergence, choosing the least
dyadic exponent that contains the chain length. -/
theorem radius_le_add_clog_of_chain_avoids_ball {δ D R C : ℝ}
    (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ) (w : X) (y : ℕ → X)
    (N : ℕ) (hNpos : 0 < N)
    (hedge : ∀ i, i < N → dist (y i) (y (i + 1)) ≤ D)
    (havoid : ∀ i, i ≤ N → R ≤ dist (y i) w)
    (hend : gromovProduct (y 0) (y N) w ≤ C) :
    R ≤ C + D / 2 + Nat.clog 2 N * δ := by
  exact radius_le_of_chain_avoids_ball hδ hδ0 w y N (Nat.clog 2 N)
    hNpos (Nat.le_pow_clog (by norm_num) N) hedge havoid hend

/-- **Exterior excursion components have only logarithmic room.**  Suppose an
`N`-edge chain stays outside the radius-`R` ball, its two endpoints lie within
one edge length `D` of the sphere, and positive progress separates the
endpoints by at least `lN`.  The radius cancels from the dyadic divergence
bound, leaving a linear-versus-logarithmic inequality for `N`.

This is the specialized interior Morse bootstrap: maximal exterior components
of a loxodromic orbit satisfy exactly these hypotheses. -/
theorem linear_length_le_of_excursion_chain {δ D R l : ℝ}
    (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ) (w : X) (y : ℕ → X)
    (N : ℕ) (hNpos : 0 < N)
    (hedge : ∀ i, i < N → dist (y i) (y (i + 1)) ≤ D)
    (havoid : ∀ i, i ≤ N → R ≤ dist (y i) w)
    (hends : dist (y 0) w ≤ R + D ∧ dist (y N) w ≤ R + D)
    (hprogress : l * N ≤ dist (y 0) (y N)) :
    l * N / 2 ≤ 3 * D / 2 + Nat.clog 2 N * δ := by
  have hend : gromovProduct (y 0) (y N) w ≤ R + D - l * N / 2 := by
    unfold gromovProduct
    linarith
  have hrad := radius_le_add_clog_of_chain_avoids_ball hδ hδ0 w y N
    hNpos hedge havoid hend
  linarith

/-- Powers of two eventually dominate every nonnegative affine function.  This
is the numerical cutoff used by the dyadic Morse bootstrap. -/
theorem eventually_affine_lt_pow_two (A B : ℝ) :
    ∀ᶠ k : ℕ in Filter.atTop, A * k + B < (2 : ℝ) ^ k := by
  have hk := tendsto_pow_const_div_const_pow_of_one_lt 1 (r := (2 : ℝ))
    (by norm_num)
  have hzero := tendsto_pow_const_div_const_pow_of_one_lt 0 (r := (2 : ℝ))
    (by norm_num)
  have ht : Filter.Tendsto
      (fun k : ℕ => (A * k + B) / (2 : ℝ) ^ k)
      Filter.atTop (nhds 0) := by
    convert (hk.const_mul A).add (hzero.const_mul B) using 1
    · funext k
      field_simp
    · ring
  filter_upwards [ht.eventually_lt_const zero_lt_one] with k hklt
  have hpow : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  rw [div_lt_iff₀ hpow] at hklt
  simpa using hklt

/-- A concrete natural-number form of the dyadic bootstrap: no affine
multiple of `clog` can dominate every radius. -/
theorem exists_nat_gt_const_add_mul_clog (A B c d : ℕ) :
    ∃ r : ℕ, c + d * Nat.clog 2 (A * r + B) < r := by
  have hev := eventually_affine_lt_pow_two
    ((A * (d + 1) : ℕ) : ℝ) (B : ℝ)
  rw [Filter.eventually_atTop] at hev
  obtain ⟨K, hK⟩ := hev
  let k : ℕ := max K (c + 1)
  have hkK : K ≤ k := le_max_left _ _
  have hkc : c < k := lt_of_lt_of_le (Nat.lt_succ_self c) (le_max_right _ _)
  have hpR := hK k hkK
  have hp : A * ((d + 1) * k) + B < 2 ^ k := by
    have hassoc : A * ((d + 1) * k) + B = (A * (d + 1)) * k + B := by
      ring
    rw [hassoc]
    exact_mod_cast hpR
  have hclog : Nat.clog 2 (A * ((d + 1) * k) + B) ≤ k :=
    Nat.clog_le_of_le_pow (Nat.le_of_lt hp)
  refine ⟨(d + 1) * k, ?_⟩
  calc
    c + d * Nat.clog 2 (A * ((d + 1) * k) + B)
        ≤ c + d * k := Nat.add_le_add_left (Nat.mul_le_mul_left d hclog) c
    _ < k + d * k := Nat.add_lt_add_right hkc (d * k)
    _ = (d + 1) * k := by
      simp only [Nat.add_mul, Nat.one_mul]
      omega

/-- An affine function of the binary ceiling logarithm is eventually strictly
smaller than its argument. -/
theorem eventually_const_add_mul_clog_lt (c d : ℕ) :
    ∃ M : ℕ, ∀ N : ℕ, M < N → c + d * Nat.clog 2 N < N := by
  have hev := eventually_affine_lt_pow_two (d : ℝ) (c + d : ℕ)
  rw [Filter.eventually_atTop] at hev
  obtain ⟨K, hK⟩ := hev
  refine ⟨2 ^ (K + 1), fun N hMN => ?_⟩
  have hclog : K + 1 < Nat.clog 2 N := by
    rw [Nat.lt_clog_iff_pow_lt (by norm_num)]
    exact hMN
  have hpow1 : 1 < 2 ^ (K + 1) :=
    Nat.one_lt_pow (Nat.succ_ne_zero K) (by norm_num)
  have hN1 : 1 < N := lt_of_lt_of_le hpow1 (Nat.le_of_lt hMN)
  let t : ℕ := (Nat.clog 2 N).pred
  have htK : K ≤ t := by
    dsimp [t]
    omega
  have hpR := hK t htK
  have hp : d * t + (c + d) < 2 ^ t := by exact_mod_cast hpR
  have htN : 2 ^ t < N := by
    dsimp [t]
    exact Nat.pow_pred_clog_lt_self (by norm_num) hN1
  have ht : t + 1 = Nat.clog 2 N := by
    dsimp [t]
    have : 0 < Nat.clog 2 N := Nat.clog_pos (by norm_num) hN1
    omega
  calc
    c + d * Nat.clog 2 N = c + d * (t + 1) := by rw [ht]
    _ = d * t + (c + d) := by
      simp only [Nat.mul_add, Nat.mul_one]
      omega
    _ < 2 ^ t := hp
    _ < N := htN

/-- Consequently, a positive linear function cannot be bounded by a constant
plus `δ·clog₂` for arbitrarily large natural arguments. -/
theorem exists_bound_of_linear_le_add_clog {l D δ : ℝ} (hl : 0 < l) :
    ∃ M : ℕ, ∀ N : ℕ,
      l * N / 2 ≤ 3 * D / 2 + Nat.clog 2 N * δ → N ≤ M := by
  obtain ⟨c, hc⟩ := exists_nat_ge (3 * D / l)
  obtain ⟨d, hd⟩ := exists_nat_ge (2 * δ / l)
  obtain ⟨M, hM⟩ := eventually_const_add_mul_clog_lt c d
  refine ⟨M, fun N hlin => ?_⟩
  have hscaled : (N : ℝ) ≤
      3 * D / l + (2 * δ / l) * Nat.clog 2 N := by
    have hl0 : l ≠ 0 := ne_of_gt hl
    calc
      (N : ℝ) = (2 / l) * (l * N / 2) := by field_simp
      _ ≤ (2 / l) * (3 * D / 2 + Nat.clog 2 N * δ) :=
        mul_le_mul_of_nonneg_left hlin (by positivity)
      _ = 3 * D / l + (2 * δ / l) * Nat.clog 2 N := by
        field_simp [hl0]
  have hlog0 : (0 : ℝ) ≤ Nat.clog 2 N := by positivity
  have hupper : (N : ℝ) ≤ c + d * Nat.clog 2 N := by
    have hdmul := mul_le_mul_of_nonneg_right hd hlog0
    linarith
  have hupperNat : N ≤ c + d * Nat.clog 2 N := by exact_mod_cast hupper
  by_contra hNM
  have hstrict := hM N (lt_of_not_ge hNM)
  omega

/-- Uniform form of the exterior-component estimate. -/
theorem exists_bound_excursion_chain_length {δ D l : ℝ}
    (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ) (hl : 0 < l) :
    ∃ M : ℕ, ∀ (R : ℝ) (w : X) (y : ℕ → X) (N : ℕ),
      0 < N →
      (∀ i, i < N → dist (y i) (y (i + 1)) ≤ D) →
      (∀ i, i ≤ N → R ≤ dist (y i) w) →
      dist (y 0) w ≤ R + D ∧ dist (y N) w ≤ R + D →
      l * N ≤ dist (y 0) (y N) → N ≤ M := by
  obtain ⟨M, hM⟩ := exists_bound_of_linear_le_add_clog
    (l := l) (D := D) (δ := δ) hl
  refine ⟨M, fun R w y N hN hedge havoid hends hprogress => ?_⟩
  exact hM N (linear_length_le_of_excursion_chain hδ hδ0 w y N hN
    hedge havoid hends hprogress)

/-- Scanning left from an exterior vertex in a finite real-valued path finds
the first exterior vertex after the path last entered the ball. -/
theorem exists_left_excursion_boundary (q : ℕ → ℝ) {D R : ℝ} :
    ∀ {j : ℕ}, q 0 < R → R ≤ q j →
      (∀ i, i < j → q (i + 1) ≤ q i + D) →
      ∃ a : ℕ, a ≤ j ∧ q a ≤ R + D ∧
        ∀ i : ℕ, a ≤ i → i ≤ j → R ≤ q i := by
  intro j
  induction j with
  | zero =>
      intro h0 hj _
      linarith
  | succ n ih =>
      intro h0 hj hstep
      by_cases hn : R ≤ q n
      · obtain ⟨a, haj, haR, hall⟩ := ih h0 hn
          (fun i hi => hstep i (by omega))
        refine ⟨a, by omega, haR, fun i hai hij => ?_⟩
        rcases lt_or_eq_of_le hij with hi | rfl
        · exact hall i hai (by omega)
        · exact hj
      · refine ⟨n + 1, le_rfl, ?_, fun i hai hij => ?_⟩
        · have hs := hstep n (by omega)
          linarith
        · have hi : i = n + 1 := by omega
          simpa [hi] using hj

/-- The analogous scan to the right, parametrised by the remaining number of
edges. -/
theorem exists_right_excursion_boundary (q : ℕ → ℝ) {D R : ℝ} :
    ∀ (d j : ℕ), q (j + d) < R → R ≤ q j →
      (∀ i, i < d → q (j + i) ≤ q (j + i + 1) + D) →
      ∃ b : ℕ, b ≤ d ∧ q (j + b) ≤ R + D ∧
        ∀ i : ℕ, i ≤ b → R ≤ q (j + i) := by
  intro d
  induction d with
  | zero =>
      intro j hend hj _
      simp only [add_zero] at hend
      linarith
  | succ n ih =>
      intro j hend hj hstep
      by_cases hnext : R ≤ q (j + 1)
      · have hend' : q ((j + 1) + n) < R := by
          have heq : (j + 1) + n = j + (n + 1) := by omega
          rw [heq]
          exact hend
        have hstep' : ∀ i, i < n →
            q ((j + 1) + i) ≤ q ((j + 1) + i + 1) + D := by
          intro i hi
          have hs := hstep (i + 1) (by omega)
          have heq0 : j + (i + 1) = (j + 1) + i := by omega
          simpa only [heq0] using hs
        obtain ⟨b, hbn, hbR, hall⟩ := ih (j + 1) hend' hnext hstep'
        refine ⟨b + 1, by omega, ?_, fun i hi => ?_⟩
        · have heq : (j + 1) + b = j + (b + 1) := by omega
          rwa [← heq]
        · rcases Nat.eq_zero_or_pos i with rfl | hi0
          · simpa using hj
          · have := hall (i - 1) (by omega)
            have heq : (j + 1) + (i - 1) = j + i := by omega
            rwa [heq] at this
      · refine ⟨0, by omega, ?_, fun i hi => ?_⟩
        · have hs := hstep 0 (by omega)
          simp only [add_zero] at hs ⊢
          linarith
        · have hi0 : i = 0 := by omega
          simpa [hi0] using hj

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

/-- Reversing an arclength geodesic on `[0,D]` gives an arclength geodesic
with the opposite orientation. -/
theorem IsGeodesicSegment.reverse_zero {f : ℝ → X} {D : ℝ}
    (_hD : 0 ≤ D) (h : IsGeodesicSegment f 0 D) :
    IsGeodesicSegment (fun t => f (D - t)) 0 D := by
  intro s hs t ht
  have hs' : D - s ∈ Set.Icc (0 : ℝ) D := by
    constructor <;> linarith [hs.1, hs.2]
  have ht' : D - t ∈ Set.Icc (0 : ℝ) D := by
    constructor <;> linarith [ht.1, ht.2]
  rw [h (D - s) hs' (D - t) ht']
  have he : D - s - (D - t) = -(s - t) := by ring
  rw [he, abs_neg]

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
  have hev := hg.isEscaping.eventually_ge_atTop R
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

/-- An infinite-order element commuting with a loxodromic element has an orbit
escaping every bounded set under an acylindrical action.

Indeed `finite_centralizer_ball` says that every bounded ball contains only
finitely many elements of the centralizer.  The nonnegative powers of an
infinite-order element are distinct, so only finitely many can remain in any
fixed ball.  This is exactly convergence of their displacement to infinity. -/
theorem isEscaping_of_commutes_of_not_isOfFinOrder
    (hiso : IsIsometricAction G X) (hacy : IsAcylindrical G X)
    {g c : G} {x : X} (hg : IsLoxodromic g x) (hcg : Commute c g)
    (hc : ¬ IsOfFinOrder c) : IsEscaping c x := by
  rw [IsEscaping, Filter.tendsto_atTop]
  intro B
  let ε : ℝ := max (B + 1) 1
  have hε : 0 < ε := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hBε : B < ε := lt_of_lt_of_le (lt_add_one B) (le_max_left _ _)
  have hfinite :
      {k : G | Commute k g ∧ dist x (k • x) ≤ ε}.Finite :=
    finite_centralizer_ball hiso hacy hg hε
  have hinj : Function.Injective (fun n : ℕ => c ^ n) :=
    injective_pow_iff_not_isOfFinOrder.mpr hc
  have hpre :
      {n : ℕ | c ^ n ∈ {k : G | Commute k g ∧ dist x (k • x) ≤ ε}}.Finite :=
    hfinite.preimage hinj.injOn
  have hev : ∀ᶠ n : ℕ in Filter.atTop,
      n ∉ {n : ℕ | c ^ n ∈ {k : G |
        Commute k g ∧ dist x (k • x) ≤ ε}} := by
    rw [← Nat.cofinite_eq_atTop]
    exact hpre.eventually_cofinite_notMem
  filter_upwards [hev] with n hn
  by_contra hnot
  apply hn
  exact ⟨hcg.pow_left n, le_trans (le_of_not_ge hnot) (le_of_lt hBε)⟩

/-- **The concrete shared-elementary-axis branch.**

No elementary-closure predicate is used.  The input is the power relation that
such a shared axis must eventually provide:

`c gᵐ c⁻¹ = gⁿ`, with `m ≠ n`.

The commutator relation puts the nonzero loxodromic power `gⁿ⁻ᵐ` in the
normal subgroup.  In the parallel case `m = n`, finite centralizer balls only
give escape of `c`; the missing common-axis theorem must supply linear progress
before `c` may honestly be called loxodromic. -/
theorem exists_loxodromic_mem_of_common_zpow
    (hiso : IsIsometricAction G X) {S : Subgroup G}
    {g c : G} {x : X} (hcS : c ∈ S) (hg : IsLoxodromic g x)
    {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hpower : c ^ a = g ^ b) :
    ∃ q ∈ S, IsLoxodromic q x := by
  refine ⟨c, hcS, ?_⟩
  exact isLoxodromic_of_common_zpow hiso hg hb ha hpower.symm

theorem exists_loxodromic_mem_of_conj_zpow_eq_zpow_of_ne
    (hiso : IsIsometricAction G X) {S : Subgroup G} [S.Normal]
    {g c : G} {x : X} (hcS : c ∈ S)
    (hg : IsLoxodromic g x) {m n : ℤ} (hmn : m ≠ n)
    (hpower : c * g ^ m * c⁻¹ = g ^ n) :
    ∃ q ∈ S, IsLoxodromic q x := by
  have hdiff : n - m ≠ 0 := sub_ne_zero.mpr (Ne.symm hmn)
  have hmemComm : c * g ^ m * c⁻¹ * (g ^ m)⁻¹ ∈ S := by
    have hconj : g ^ m * c⁻¹ * (g ^ m)⁻¹ ∈ S :=
      (inferInstance : S.Normal).conj_mem c⁻¹ (S.inv_mem hcS) (g ^ m)
    simpa only [mul_assoc] using S.mul_mem hcS hconj
  have heq : c * g ^ m * c⁻¹ * (g ^ m)⁻¹ = g ^ (n - m) := by
    rw [hpower, ← zpow_neg, ← zpow_add]
    congr 1
  have hmem : g ^ (n - m) ∈ S := by rwa [heq] at hmemComm
  exact ⟨g ^ (n - m), hmem, isLoxodromic_zpow hiso hg hdiff⟩

/-- **The first concrete dichotomy in Osin's s-normal argument.**

Let `S` be s-normal in a torsion-free group and let `g` be an ambient
loxodromic.  The twisted intersection `S ∩ g⁻¹ S g` is infinite, hence contains
a nonidentity element `c`.  If `c` commutes with `g`, torsion-freeness and the
preceding theorem make `c` escaping.  Otherwise `c` and its `g`-conjugate are
both in `S`, giving the noncommuting configuration consumed by the next stage
of the product argument.

Thus the centralizing branch still visibly requires the common-axis theorem. -/
theorem exists_escaping_or_noncommuting_of_isSNormal
    (hiso : IsIsometricAction G X) (hacy : IsAcylindrical G X)
    (htf : IsPowerTorsionFree G) {S : Subgroup G}
    (hS : HullSuitable.IsSNormal S) {g : G} {x : X}
    (hg : IsLoxodromic g x) :
    (∃ c ∈ S, IsEscaping c x) ∨
      ∃ c ∈ S, g * c * g⁻¹ ∈ S ∧ ¬ Commute c g := by
  have hinter := hS g
  have hex : ∃ c : G,
      c ∈ {c : G | c ∈ S ∧ g * c * g⁻¹ ∈ S} ∧ c ≠ 1 := by
    by_contra hnone
    have hsub : {c : G | c ∈ S ∧ g * c * g⁻¹ ∈ S} ⊆ ({1} : Set G) := by
      intro c hc
      have hc1 : c = 1 := by
        by_contra hc1
        exact hnone ⟨c, hc, hc1⟩
      simp [hc1]
    exact hinter (Set.Finite.subset (Set.finite_singleton 1) hsub)
  obtain ⟨c, ⟨hcS, hgcS⟩, hc1⟩ := hex
  by_cases hcomm : Commute c g
  · left
    exact ⟨c, hcS, isEscaping_of_commutes_of_not_isOfFinOrder
      hiso hacy hg hcomm (htf.not_isOfFinOrder hc1)⟩
  · right
    exact ⟨c, hcS, hgcS, hcomm⟩

/-- The noncommuting branch produces a concrete nontrivial product inside the
subgroup: the difference between `g c g⁻¹` and `c` is their commutator.  This is
the candidate to which a bounded-backtracking/ping-pong estimate can be
applied; unlike `gⁿ c`, it is guaranteed to remain in `S`. -/
theorem nontrivial_commutator_mem_of_mem_conjugate {S : Subgroup G}
    {g c : G} (hcS : c ∈ S) (hgcS : g * c * g⁻¹ ∈ S)
    (hncomm : ¬ Commute c g) :
    g * c * g⁻¹ * c⁻¹ ∈ S ∧ g * c * g⁻¹ * c⁻¹ ≠ 1 := by
  constructor
  · exact S.mul_mem hgcS (S.inv_mem hcS)
  · intro htriv
    apply hncomm
    have hcomm : Commute g c := commutatorElement_eq_one_iff_commute.mp (by
      rw [commutatorElement_def]
      exact htriv)
    exact hcomm.symm

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

/-- A finite family of strict real inequalities has a uniform positive
margin.  This elementary compactness substitute is used when passing from
`not (∃ i, q i ≤ E)` to a closed lower bound suitable for the dyadic chain
estimate. -/
theorem exists_pos_uniform_margin_fin (q : ℕ → ℝ) (E : ℝ) :
    ∀ N : ℕ, (∀ i, i ≤ N → E < q i) →
      ∃ eta : ℝ, 0 < eta ∧ ∀ i, i ≤ N → E + eta ≤ q i := by
  intro N
  induction N with
  | zero =>
      intro h
      refine ⟨(q 0 - E) / 2, by linarith [h 0 le_rfl], ?_⟩
      intro i hi
      have hi0 : i = 0 := by omega
      subst i
      linarith [h 0 le_rfl]
  | succ N ih =>
      intro h
      obtain ⟨eta, heta, hprev⟩ := ih (fun i hi => h i (by omega))
      let eta' : ℝ := min eta ((q (N + 1) - E) / 2)
      have hnew : E < q (N + 1) := h (N + 1) le_rfl
      have heta' : 0 < eta' := lt_min heta (by linarith)
      refine ⟨eta', heta', fun i hi => ?_⟩
      by_cases hiN : i ≤ N
      · have hetaLe : eta' ≤ eta := min_le_left _ _
        linarith [hprev i hiN]
      · have hieq : i = N + 1 := by omega
        subst i
        have hle : eta' ≤ (q (N + 1) - E) / 2 := min_le_right _ _
        linarith

/-- Every point of a geodesic spanning a bounded-step chain is logarithmically
close to some vertex of the chain.  If all vertices avoided a slightly larger
ball around that geodesic point, `radius_le_of_chain_avoids_ball` would force
that radius to be no larger than itself minus one, since the endpoint Gromov
product based at a point of their geodesic is zero. -/
theorem exists_chain_point_dist_le_of_mem_geodesic {δ D : ℝ}
    (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ)
    (y : ℕ → X) (N k : ℕ) (hNpos : 0 < N) (hN : N ≤ 2 ^ k)
    (hedge : ∀ i, i < N → dist (y i) (y (i + 1)) ≤ D)
    {f : ℝ → X} (hf : IsGeodesicSegment f 0 (dist (y 0) (y N)))
    (hf0 : f 0 = y 0) (hf1 : f (dist (y 0) (y N)) = y N)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) (dist (y 0) (y N))) :
    ∃ i : ℕ, i ≤ N ∧ dist (y i) (f s) ≤ D / 2 + k * δ := by
  by_contra hnone
  have hstrict : ∀ i : ℕ, i ≤ N →
      D / 2 + k * δ < dist (y i) (f s) := by
    intro i hi
    have hnot : ¬ dist (y i) (f s) ≤ D / 2 + k * δ := by
      intro hle
      exact hnone ⟨i, hi, hle⟩
    exact lt_of_not_ge hnot
  obtain ⟨eta, heta, hfar⟩ := exists_pos_uniform_margin_fin
    (fun i => dist (y i) (f s)) (D / 2 + k * δ) N hstrict
  have hend : gromovProduct (y 0) (y N) (f s) ≤ 0 := by
    have h := gromovProduct_le_dist_of_mem_geodesic
      (a := 0) (b := dist (y 0) (y N)) (s := s)
      dist_nonneg hs hf (f s)
    rw [hf0, hf1, dist_self] at h
    exact h
  have hrad := radius_le_of_chain_avoids_ball hδ hδ0 (f s) y N k
    hNpos hN hedge hfar hend
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

/-- **Geodesic triangles are `3δ`-thin.**  A point on the `A--C` side lies
within `3δ` of one of the other two sides.  At that point
`(A|C)=0`; four-point hyperbolicity makes one of `(A|B)` and `(B|C)` at most
`δ`, and the Gromov-product/geodesic dictionary costs another `2δ`. -/
theorem exists_close_on_other_side_of_geodesic_triangle {δ : ℝ}
    (hδ : IsHyperbolicSpace δ X) (_hδ0 : 0 ≤ δ)
    {A B C : X}
    {fAC fAB fBC : ℝ → X}
    (hAC : IsGeodesicSegment fAC 0 (dist A C))
    (hAC0 : fAC 0 = A) (hAC1 : fAC (dist A C) = C)
    (hAB : IsGeodesicSegment fAB 0 (dist A B))
    (hAB0 : fAB 0 = A) (hAB1 : fAB (dist A B) = B)
    (hBC : IsGeodesicSegment fBC 0 (dist B C))
    (hBC0 : fBC 0 = B) (hBC1 : fBC (dist B C) = C)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) (dist A C)) :
    (∃ s ∈ Set.Icc (0 : ℝ) (dist A B),
      dist (fAC t) (fAB s) ≤ 3 * δ) ∨
    (∃ s ∈ Set.Icc (0 : ℝ) (dist B C),
      dist (fAC t) (fBC s) ≤ 3 * δ) := by
  have hzero : gromovProduct A C (fAC t) = 0 := by
    have h := gromovProduct_le_dist_of_mem_geodesic dist_nonneg ht hAC (fAC t)
    rw [hAC0, hAC1, dist_self] at h
    exact le_antisymm h (gromovProduct_nonneg _ _ _)
  have hfour := hδ (fAC t) A B C
  rw [hzero] at hfour
  have hmin : min (gromovProduct A B (fAC t))
      (gromovProduct B C (fAC t)) ≤ δ := by linarith
  rcases min_le_iff.mp hmin with hleft | hright
  · left
    obtain ⟨s, hs, hnear⟩ := exists_mem_geodesic_dist_le hδ hAB hAB0 hAB1
      (fAC t)
    exact ⟨s, hs, by linarith⟩
  · right
    obtain ⟨s, hs, hnear⟩ := exists_mem_geodesic_dist_le hδ hBC hBC0 hBC1
      (fAC t)
    exact ⟨s, hs, by linarith⟩

/-- If a vertex is farther than `r + 3δ` from the opposite side, then the
point distance `r` down either adjacent side is `3δ`-close to the other
adjacent side.  This is the fellow-travelling form of thin triangles used to
extract a detour from a large orbit excursion. -/
theorem exists_close_on_adjacent_side_of_far_vertex {δ r : ℝ}
    (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ)
    {A B C : X} {fAB fAC fCB : ℝ → X}
    (hAB : IsGeodesicSegment fAB 0 (dist A B))
    (hAB0 : fAB 0 = A) (hAB1 : fAB (dist A B) = B)
    (hAC : IsGeodesicSegment fAC 0 (dist A C))
    (hAC0 : fAC 0 = A) (hAC1 : fAC (dist A C) = C)
    (hCB : IsGeodesicSegment fCB 0 (dist C B))
    (hCB0 : fCB 0 = C) (hCB1 : fCB (dist C B) = B)
    (hr0 : 0 ≤ r) (hrAB : r ≤ dist A B)
    (hfar : ∀ s ∈ Set.Icc (0 : ℝ) (dist A C),
      r + 3 * δ < dist B (fAC s)) :
    ∃ s ∈ Set.Icc (0 : ℝ) (dist C B),
      dist (fAB (dist A B - r)) (fCB s) ≤ 3 * δ := by
  have ht : dist A B - r ∈ Set.Icc (0 : ℝ) (dist A B) := by
    constructor <;> linarith [dist_nonneg (x := A) (y := B)]
  have hBr : dist B (fAB (dist A B - r)) = r := by
    have h := hAB (dist A B) ⟨dist_nonneg, le_rfl⟩
      (dist A B - r) ht
    rw [hAB1] at h
    rw [h, abs_of_nonneg (by linarith)]
    ring
  have hthin := exists_close_on_other_side_of_geodesic_triangle hδ hδ0
    hAB hAB0 hAB1 hAC hAC0 hAC1 hCB hCB0 hCB1 ht
  rcases hthin with hglobal | hadjacent
  · obtain ⟨s, hs, hnear⟩ := hglobal
    have htri := dist_triangle B (fAB (dist A B - r)) (fAC s)
    rw [hBr] at htri
    exact False.elim (by linarith [hfar s hs])
  · exact hadjacent

/-- Synchronous form of the far-vertex fellow-travelling lemma.  At equal
distance `r` from the far vertex, the two adjacent sides are `6δ`-close. -/
theorem dist_equal_radius_sides_le_of_far_vertex {δ r : ℝ}
    (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ)
    {A B C : X} {fAB fAC fCB : ℝ → X}
    (hAB : IsGeodesicSegment fAB 0 (dist A B))
    (hAB0 : fAB 0 = A) (hAB1 : fAB (dist A B) = B)
    (hAC : IsGeodesicSegment fAC 0 (dist A C))
    (hAC0 : fAC 0 = A) (hAC1 : fAC (dist A C) = C)
    (hCB : IsGeodesicSegment fCB 0 (dist C B))
    (hCB0 : fCB 0 = C) (hCB1 : fCB (dist C B) = B)
    (hr0 : 0 ≤ r) (hrAB : r ≤ dist A B) (hrCB : r ≤ dist C B)
    (hfar : ∀ s ∈ Set.Icc (0 : ℝ) (dist A C),
      r + 3 * δ < dist B (fAC s)) :
    dist (fAB (dist A B - r)) (fCB (dist C B - r)) ≤ 6 * δ := by
  obtain ⟨s, hs, hus⟩ := exists_close_on_adjacent_side_of_far_vertex
    hδ hδ0 hAB hAB0 hAB1 hAC hAC0 hAC1 hCB hCB0 hCB1 hr0 hrAB hfar
  have hBr : dist B (fAB (dist A B - r)) = r := by
    have ht : dist A B - r ∈ Set.Icc (0 : ℝ) (dist A B) := by
      constructor <;> linarith [dist_nonneg (x := A) (y := B)]
    have h := hAB (dist A B) ⟨dist_nonneg, le_rfl⟩
      (dist A B - r) ht
    rw [hAB1] at h
    rw [h, abs_of_nonneg (by linarith)]
    ring
  have hBs : dist B (fCB s) = dist C B - s := by
    have h := hCB (dist C B) ⟨dist_nonneg, le_rfl⟩ s hs
    rw [hCB1] at h
    rw [h, abs_of_nonneg (sub_nonneg.mpr hs.2)]
  have hdiff : |(dist C B - s) - r| ≤ 3 * δ := by
    have htri1 := dist_triangle B (fAB (dist A B - r)) (fCB s)
    have htri2 := dist_triangle B (fCB s) (fAB (dist A B - r))
    have hus' : dist (fCB s) (fAB (dist A B - r)) ≤ 3 * δ := by
      rwa [dist_comm]
    rw [hBr, hBs] at htri1 htri2
    rw [abs_le]
    constructor <;> linarith
  have htCB : dist C B - r ∈ Set.Icc (0 : ℝ) (dist C B) := by
    constructor <;> linarith [dist_nonneg (x := C) (y := B)]
  have hside := hCB s hs (dist C B - r) htCB
  have hside' : dist (fCB s) (fCB (dist C B - r)) ≤ 3 * δ := by
    rw [hside]
    have he : s - (dist C B - r) = -((dist C B - s) - r) := by ring
    rw [he, abs_neg]
    exact hdiff
  exact le_trans (dist_triangle _ (fCB s) _) (by linarith)

/-- Uniform initial-segment form of synchronous thinness.  If the whole
opposite side avoids the open ball of radius `R` about `B`, then the two sides
ending at `B` synchronously `6δ`-fellow-travel at every depth whose
`3δ`-enlargement is at most `R`.

This is deliberately phrased with the concrete geodesic parameters used by
the excursion argument.  In a recursive subdivision, `B` is the far orbit
vertex and `A--C` is the chord at the current scale; the conclusion can be
reused at every smaller radius without choosing new comparison points. -/
theorem dist_equal_radius_sides_le_until_opposite {delta R r : ℝ}
    (hdelta : IsHyperbolicSpace delta X) (hdelta0 : 0 ≤ delta)
    {A B C : X} {fAB fAC fCB : ℝ → X}
    (hAB : IsGeodesicSegment fAB 0 (dist A B))
    (hAB0 : fAB 0 = A) (hAB1 : fAB (dist A B) = B)
    (hAC : IsGeodesicSegment fAC 0 (dist A C))
    (hAC0 : fAC 0 = A) (hAC1 : fAC (dist A C) = C)
    (hCB : IsGeodesicSegment fCB 0 (dist C B))
    (hCB0 : fCB 0 = C) (hCB1 : fCB (dist C B) = B)
    (hsep : ∀ s ∈ Set.Icc (0 : ℝ) (dist A C), R < dist B (fAC s))
    (hr0 : 0 ≤ r) (hrAB : r ≤ dist A B) (hrCB : r ≤ dist C B)
    (hrR : r + 3 * delta ≤ R) :
    dist (fAB (dist A B - r)) (fCB (dist C B - r)) ≤ 6 * delta := by
  apply dist_equal_radius_sides_le_of_far_vertex hdelta hdelta0
    hAB hAB0 hAB1 hAC hAC0 hAC1 hCB hCB0 hCB1 hr0 hrAB hrCB
  intro s hs
  exact lt_of_le_of_lt hrR (hsep s hs)

/-- Set-valued version of the preceding lemma: the complete initial portions
of the two adjacent sides, measured backwards from the separated vertex, are
synchronously `6δ`-close.  Keeping the radius as an explicit member of an
interval makes this directly usable when a dyadic recursion selects a natural
or integer sampling radius. -/
theorem adjacent_sides_fellow_travel_while_opposite_far {delta R T : ℝ}
    (hdelta : IsHyperbolicSpace delta X) (hdelta0 : 0 ≤ delta)
    {A B C : X} {fAB fAC fCB : ℝ → X}
    (hAB : IsGeodesicSegment fAB 0 (dist A B))
    (hAB0 : fAB 0 = A) (hAB1 : fAB (dist A B) = B)
    (hAC : IsGeodesicSegment fAC 0 (dist A C))
    (hAC0 : fAC 0 = A) (hAC1 : fAC (dist A C) = C)
    (hCB : IsGeodesicSegment fCB 0 (dist C B))
    (hCB0 : fCB 0 = C) (hCB1 : fCB (dist C B) = B)
    (hsep : ∀ s ∈ Set.Icc (0 : ℝ) (dist A C), R < dist B (fAC s))
    (hTAB : T ≤ dist A B) (hTCB : T ≤ dist C B)
    (hTR : T + 3 * delta ≤ R) :
    ∀ r ∈ Set.Icc (0 : ℝ) T,
      dist (fAB (dist A B - r)) (fCB (dist C B - r)) ≤ 6 * delta := by
  intro r hr
  apply dist_equal_radius_sides_le_until_opposite hdelta hdelta0
    hAB hAB0 hAB1 hAC hAC0 hAC1 hCB hCB0 hCB1 hsep hr.1
  · exact le_trans hr.2 hTAB
  · exact le_trans hr.2 hTCB
  · linarith [hr.2, hTR]

/-- **Dyadic sampling across a far excursion vertex.**  Let `y 0,…,y N` be
a bounded-step chain and let `y j` be far from the endpoint chord.  At depth
`r` from `y j`, synchronous thinness gives two `6δ`-close points on the
adjacent geodesics.  The logarithmic chain-density lemma then replaces those
geodesic points by one chain vertex on each side of `j`.

The conclusion records both estimates needed by the recursive Morse
bootstrap: the sampled vertices are close to each other, while each is still
almost distance `r` from the excursion vertex.  There is no Morse or
local-to-global premise in this statement; all error terms are the explicit
dyadic errors `D/2 + kδ`. -/
theorem exists_chain_vertices_across_far_vertex {delta D r : ℝ}
    (hdelta : IsHyperbolicSpace delta X) (hdelta0 : 0 ≤ delta)
    (y : ℕ → X) {N j kL kR : ℕ} (hj0 : 0 < j) (hjN : j < N)
    (hjpow : j ≤ 2 ^ kL) (hRpow : N - j ≤ 2 ^ kR)
    (hedge : ∀ i, i < N → dist (y i) (y (i + 1)) ≤ D)
    {fAB fAC fCB : ℝ → X}
    (hAB : IsGeodesicSegment fAB 0 (dist (y 0) (y j)))
    (hAB0 : fAB 0 = y 0) (hAB1 : fAB (dist (y 0) (y j)) = y j)
    (hAC : IsGeodesicSegment fAC 0 (dist (y 0) (y N)))
    (hAC0 : fAC 0 = y 0) (hAC1 : fAC (dist (y 0) (y N)) = y N)
    (hCB : IsGeodesicSegment fCB 0 (dist (y N) (y j)))
    (hCB0 : fCB 0 = y N) (hCB1 : fCB (dist (y N) (y j)) = y j)
    (hr0 : 0 ≤ r) (hrL : r ≤ dist (y 0) (y j))
    (hrR : r ≤ dist (y N) (y j))
    (hfar : ∀ s ∈ Set.Icc (0 : ℝ) (dist (y 0) (y N)),
      r + 3 * delta < dist (y j) (fAC s)) :
    ∃ i q : ℕ,
      i ≤ j ∧ q ≤ N - j ∧
      dist (y i) (fAB (dist (y 0) (y j) - r)) ≤ D / 2 + kL * delta ∧
      dist (y (j + q)) (fCB (dist (y N) (y j) - r)) ≤
        D / 2 + kR * delta ∧
      dist (y i) (y (j + q)) ≤
        D + (kL + kR) * delta + 6 * delta ∧
      r ≤ dist (y i) (y j) + (D / 2 + kL * delta) ∧
      r ≤ dist (y (j + q)) (y j) + (D / 2 + kR * delta) := by
  let z : ℕ → X := fun q => y (j + q)
  let qCB : ℝ → X := fun t => fCB (dist (y N) (y j) - t)
  have hNj0 : 0 < N - j := Nat.sub_pos_of_lt hjN
  have hedgeL : ∀ i, i < j → dist (y i) (y (i + 1)) ≤ D := by
    intro i hi
    exact hedge i (lt_trans hi hjN)
  have hedgeR : ∀ q, q < N - j → dist (z q) (z (q + 1)) ≤ D := by
    intro q hq
    have he := hedge (j + q) (by omega)
    simpa only [z, Nat.add_assoc] using he
  have hz0 : z 0 = y j := by simp [z]
  have hzN : z (N - j) = y N := by
    simp only [z]
    congr 1
    omega
  have hqgeo : IsGeodesicSegment qCB 0 (dist (y j) (y N)) := by
    have hrev := IsGeodesicSegment.reverse_zero
      (dist_nonneg (x := y N) (y := y j)) hCB
    dsimp only [qCB]
    rw [dist_comm (y j) (y N)]
    exact hrev
  have hq0 : qCB 0 = y j := by simp [qCB, hCB1]
  have hq1 : qCB (dist (y j) (y N)) = y N := by
    simp [qCB, dist_comm (y j) (y N), hCB0]
  have hqgeoZ : IsGeodesicSegment qCB 0 (dist (z 0) (z (N - j))) := by
    rw [hz0, hzN]
    exact hqgeo
  have hq0Z : qCB 0 = z 0 := by rwa [hz0]
  have hq1Z : qCB (dist (z 0) (z (N - j))) = z (N - j) := by
    rw [hz0, hzN]
    exact hq1
  have hsL : dist (y 0) (y j) - r ∈
      Set.Icc (0 : ℝ) (dist (y 0) (y j)) := by
    constructor <;> linarith [dist_nonneg (x := y 0) (y := y j)]
  have hsR : r ∈ Set.Icc (0 : ℝ) (dist (y j) (y N)) := by
    constructor
    · exact hr0
    · rwa [dist_comm]
  have hsRZ : r ∈ Set.Icc (0 : ℝ) (dist (z 0) (z (N - j))) := by
    rw [hz0, hzN]
    exact hsR
  obtain ⟨i, hi, hiNear⟩ := exists_chain_point_dist_le_of_mem_geodesic
    hdelta hdelta0 y j kL hj0 hjpow hedgeL hAB hAB0 hAB1 hsL
  obtain ⟨q, hq, hqNear⟩ := exists_chain_point_dist_le_of_mem_geodesic
    hdelta hdelta0 z (N - j) kR hNj0 hRpow hedgeR hqgeoZ hq0Z hq1Z hsRZ
  have hsync := dist_equal_radius_sides_le_of_far_vertex
    hdelta hdelta0 hAB hAB0 hAB1 hAC hAC0 hAC1 hCB hCB0 hCB1
    hr0 hrL hrR hfar
  have hqNear' : dist (y (j + q))
      (fCB (dist (y N) (y j) - r)) ≤ D / 2 + kR * delta := by
    simpa [z, qCB] using hqNear
  have hclose : dist (y i) (y (j + q)) ≤
      D + (kL + kR) * delta + 6 * delta := by
    have ht := dist_triangle4 (y i)
      (fAB (dist (y 0) (y j) - r))
      (fCB (dist (y N) (y j) - r)) (y (j + q))
    rw [dist_comm (fCB (dist (y N) (y j) - r)) (y (j + q))] at ht
    linarith
  have hleftRadius : dist (y j)
      (fAB (dist (y 0) (y j) - r)) = r := by
    have ht := hAB (dist (y 0) (y j)) ⟨dist_nonneg, le_rfl⟩
      (dist (y 0) (y j) - r) hsL
    rw [hAB1] at ht
    rw [ht, abs_of_nonneg (by linarith)]
    ring
  have hrightRadius : dist (y j)
      (fCB (dist (y N) (y j) - r)) = r := by
    have hs : dist (y N) (y j) - r ∈
        Set.Icc (0 : ℝ) (dist (y N) (y j)) := by
      constructor <;> linarith [dist_nonneg (x := y N) (y := y j)]
    have ht := hCB (dist (y N) (y j)) ⟨dist_nonneg, le_rfl⟩
      (dist (y N) (y j) - r) hs
    rw [hCB1] at ht
    rw [ht, abs_of_nonneg (by linarith)]
    ring
  refine ⟨i, q, hi, hq, hiNear, hqNear', hclose, ?_, ?_⟩
  · have ht := dist_triangle (y j) (y i)
      (fAB (dist (y 0) (y j) - r))
    rw [hleftRadius, dist_comm (y j) (y i)] at ht
    linarith
  · have ht := dist_triangle (y j) (y (j + q))
      (fCB (dist (y N) (y j) - r))
    rw [hrightRadius, dist_comm (y j) (y (j + q))] at ht
    linarith

/-- The distance across `n` consecutive edges of a `D`-bounded chain is at
most `nD`. -/
theorem dist_chain_le_nat_mul {D : ℝ} (y : ℕ → X) {N a n : ℕ}
    (hedge : ∀ i, i < N → dist (y i) (y (i + 1)) ≤ D)
    (han : a + n ≤ N) :
    dist (y a) (y (a + n)) ≤ n * D := by
  induction n with
  | zero => simp
  | succ n ih =>
      have ihan : a + n ≤ N := by omega
      have hnN : a + n < N := by omega
      have ht := dist_triangle (y a) (y (a + n)) (y (a + (n + 1)))
      have he := hedge (a + n) hnN
      have heq : a + n + 1 = a + (n + 1) := by omega
      rw [heq] at he
      have hi := ih ihan
      push_cast at hi ht ⊢
      linarith

/-- **Quantitative recursive-detour inequality.**  For a chain with positive
linear progress, a vertex whose endpoint chord stays farther than
`r + 3δ` cannot have arbitrarily large depth `r`.  Dyadic sampling supplies a
left/right pair separated from the vertex; bounded edge length gives a lower
bound on their parameter separation, while positive progress and synchronous
thinness give the opposing upper bound.

This is the closed numerical output of one recursive subdivision step.  Its
right-hand side depends only on the two dyadic depths `kL,kR`, not on the
chosen sample vertices. -/
theorem two_mul_progress_mul_far_radius_le {delta D l r : ℝ}
    (hdelta : IsHyperbolicSpace delta X) (hdelta0 : 0 ≤ delta)
    (hD0 : 0 ≤ D) (hl : 0 < l)
    (y : ℕ → X) {N j kL kR : ℕ} (hj0 : 0 < j) (hjN : j < N)
    (hjpow : j ≤ 2 ^ kL) (hRpow : N - j ≤ 2 ^ kR)
    (hedge : ∀ i, i < N → dist (y i) (y (i + 1)) ≤ D)
    (hprogress : ∀ a b : ℕ, a ≤ b → b ≤ N →
      l * ((b - a : ℕ) : ℝ) ≤ dist (y a) (y b))
    {fAB fAC fCB : ℝ → X}
    (hAB : IsGeodesicSegment fAB 0 (dist (y 0) (y j)))
    (hAB0 : fAB 0 = y 0) (hAB1 : fAB (dist (y 0) (y j)) = y j)
    (hAC : IsGeodesicSegment fAC 0 (dist (y 0) (y N)))
    (hAC0 : fAC 0 = y 0) (hAC1 : fAC (dist (y 0) (y N)) = y N)
    (hCB : IsGeodesicSegment fCB 0 (dist (y N) (y j)))
    (hCB0 : fCB 0 = y N) (hCB1 : fCB (dist (y N) (y j)) = y j)
    (hr0 : 0 ≤ r) (hrL : r ≤ dist (y 0) (y j))
    (hrR : r ≤ dist (y N) (y j))
    (hfar : ∀ s ∈ Set.Icc (0 : ℝ) (dist (y 0) (y N)),
      r + 3 * delta < dist (y j) (fAC s)) :
    2 * l * r ≤
      D * (D + (kL + kR) * delta + 6 * delta) +
        l * (D + (kL + kR) * delta) := by
  obtain ⟨i, q, hi, hq, hiNear, hqNear, hclose, hiRadius, hqRadius⟩ :=
    exists_chain_vertices_across_far_vertex hdelta hdelta0 y hj0 hjN
      hjpow hRpow hedge hAB hAB0 hAB1 hAC hAC0 hAC1 hCB hCB0 hCB1
      hr0 hrL hrR hfar
  have hjqN : j + q ≤ N := by omega
  have hiJq : i ≤ j + q := le_trans hi (Nat.le_add_right j q)
  have hdiff : (j + q) - i = (j - i) + q := by omega
  have hparam := hprogress i (j + q) hiJq hjqN
  rw [hdiff] at hparam
  have hparamUpper : l * (((j - i) + q : ℕ) : ℝ) ≤
      D + (kL + kR) * delta + 6 * delta :=
    le_trans hparam hclose
  have hleft : dist (y i) (y j) ≤ ((j - i : ℕ) : ℝ) * D := by
    have hiadd : i + (j - i) = j := Nat.add_sub_of_le hi
    have h := dist_chain_le_nat_mul y hedge (a := i) (n := j - i) (by omega)
    rw [hiadd] at h
    exact h
  have hright : dist (y (j + q)) (y j) ≤ (q : ℝ) * D := by
    have h := dist_chain_le_nat_mul y hedge (a := j) (n := q) hjqN
    rw [dist_comm]
    exact h
  have hradius : 2 * r ≤
      D * (((j - i) + q : ℕ) : ℝ) +
        (D + (kL + kR) * delta) := by
    have hcast : (((j - i) + q : ℕ) : ℝ) =
        ((j - i : ℕ) : ℝ) + (q : ℝ) := by push_cast; rfl
    rw [hcast]
    nlinarith
  have hscaledRadius := mul_le_mul_of_nonneg_left hradius (le_of_lt hl)
  have hscaledParam := mul_le_mul_of_nonneg_left hparamUpper hD0
  push_cast at hscaledRadius hscaledParam ⊢
  nlinarith

/-- **Endpoint stability for a bounded-turn orbit.**  Under the strict local
backtracking gap, the penultimate point of every finite orbit segment lies
within `C + 3δ` of a geodesic joining the segment's endpoints. -/
theorem exists_geodesic_point_near_penultimate_orbit {δ C : ℝ}
    (hδ : IsHyperbolicSpace δ X)
    (hiso : IsIsometricAction G X) (hgeo : IsGeodesicSpace X)
    {p : G} {x : X} (hCδ : 0 ≤ C + δ)
    (hgap : 2 * (C + δ) < dist x (p • x))
    (hturn : gromovProduct x ((p ^ 2) • x) (p • x) ≤ C)
    {N : ℕ} (hN : 0 < N) :
    ∃ (f : ℝ → X) (s : ℝ),
      IsGeodesicSegment f 0 (dist x ((p ^ N) • x)) ∧
      f 0 = x ∧ f (dist x ((p ^ N) • x)) = (p ^ N) • x ∧
      s ∈ Set.Icc (0 : ℝ) (dist x ((p ^ N) • x)) ∧
      dist ((p ^ (N - 1)) • x) (f s) ≤ C + 3 * δ := by
  let y : ℕ → X := fun n => (p ^ n) • x
  have hedge : ∀ n : ℕ,
      dist x (p • x) ≤ dist (y n) (y (n + 1)) := by
    intro n
    have h := hiso (p ^ n) x (p • x)
    rw [← mul_smul, ← pow_succ] at h
    exact le_of_eq h.symm
  have hlocal : ∀ n : ℕ,
      gromovProduct (y n) (y (n + 2)) (y (n + 1)) ≤ C := by
    intro n
    have h := gromovProduct_smul hiso (p ^ n) x ((p ^ 2) • x) (p • x)
    have htwo : p ^ n * p ^ 2 = p ^ (n + 2) := by rw [← pow_add]
    have hone : p ^ n * p = p ^ (n + 1) := by rw [← pow_succ]
    rw [← mul_smul, htwo, ← mul_smul, hone] at h
    exact h.trans_le hturn
  have hall := chain_backtracking_and_progress hδ hCδ hgap y hedge hlocal
  have hNm : N - 1 + 1 = N := Nat.sub_add_cancel hN
  have hback := (hall (N - 1)).2
  rw [hNm] at hback
  simp [y] at hback
  obtain ⟨f, hf, hf0, hf1⟩ := hgeo x ((p ^ N) • x)
  obtain ⟨s, hs, hnear⟩ := exists_mem_geodesic_dist_le hδ hf hf0 hf1
    ((p ^ (N - 1)) • x)
  refine ⟨f, s, hf, hf0, hf1, hs, ?_⟩
  linarith [hnear, hback]

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

/-- **Non-independent power orbits have arbitrarily long fellow-travelling
geodesic prefixes.**

This is the first geometric half of the common-power theorem.  Negating the
definition of `Independent` produces power endpoints with arbitrarily large
Gromov product.  Geodesics from the common basepoint to those endpoints then
remain `4δ`-close for any prescribed initial length `T`.

No boundary or elementary-closure notion occurs in the statement. -/
theorem exists_long_fellow_geodesics_of_not_independent {δ : ℝ}
    (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ) (hgeo : IsGeodesicSpace X)
    {g h : G} {x : X} (hnind : ¬ Independent g h x) (T : ℝ) (hT : 0 < T) :
    ∃ (n m : ℤ) (f q : ℝ → X),
      n ≠ 0 ∧ m ≠ 0 ∧
      IsGeodesicSegment f 0 (dist x ((g ^ n) • x)) ∧
      f 0 = x ∧ f (dist x ((g ^ n) • x)) = (g ^ n) • x ∧
      IsGeodesicSegment q 0 (dist x ((h ^ m) • x)) ∧
      q 0 = x ∧ q (dist x ((h ^ m) • x)) = (h ^ m) • x ∧
      T ≤ dist x ((g ^ n) • x) ∧ T ≤ dist x ((h ^ m) • x) ∧
      ∀ t : ℝ, 0 ≤ t → t ≤ T → dist (f t) (q t) ≤ 4 * δ := by
  have hex : ∃ n m : ℤ,
      T < gromovProduct ((g ^ n) • x) ((h ^ m) • x) x := by
    by_contra hnone
    apply hnind
    refine ⟨T, ?_⟩
    simpa only [not_exists, not_lt] using hnone
  obtain ⟨n, m, hprod⟩ := hex
  obtain ⟨f, hf, hf0, hf1⟩ := hgeo x ((g ^ n) • x)
  obtain ⟨q, hq, hq0, hq1⟩ := hgeo x ((h ^ m) • x)
  have hleft : T ≤ dist x ((g ^ n) • x) := by
    have hb := gromovProduct_le_right ((h ^ m) • x) ((g ^ n) • x) x
    rw [gromovProduct_comm] at hb
    rw [dist_comm ((g ^ n) • x) x] at hb
    exact le_trans (le_of_lt hprod) hb
  have hright : T ≤ dist x ((h ^ m) • x) := by
    have hb := gromovProduct_le_right ((g ^ n) • x) ((h ^ m) • x) x
    rw [dist_comm ((h ^ m) • x) x] at hb
    exact le_trans (le_of_lt hprod) hb
  have hn0 : n ≠ 0 := by
    intro hn
    subst n
    simp at hleft
    linarith
  have hm0 : m ≠ 0 := by
    intro hm
    subst m
    simp at hright
    linarith
  refine ⟨n, m, f, q, hn0, hm0, hf, hf0, hf1, hq, hq0, hq1,
    hleft, hright, ?_⟩
  intro t ht0 htT
  exact dist_le_four_delta_of_le_gromovProduct hδ hδ0 hf hf0 hf1 hq hq0 hq1
    ht0 (le_trans htT hleft) (le_trans htT hright) (le_trans htT (le_of_lt hprod))

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
