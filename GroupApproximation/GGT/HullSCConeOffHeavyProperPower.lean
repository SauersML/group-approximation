import GroupApproximation.GGT.ElementaryClosure
import GroupApproximation.GGT.HullSCConeOffCyclicReduction
import GroupApproximation.GGT.HyperbolicFreeGroupAH

/-!
# A proper power is never hyperbolically embedded over an alphabet containing a root

`GGT/HullSCConeOffCyclicReduction.lean` reduces Hull's Corollary 5.7 with Lemma
5.8, over a pair, to one geometric clause: that for **any** two independent
loxodromic elements of `Γ(G,A)` the cone-off of `A` along the cyclic subgroups
they generate is hyperbolically embedded.  That clause is
`HullSC.existsHypEmbeddedConeOff₂_of_zpowers_forall`'s hypothesis, and
`Manuscript/NonMF/TheoremCDebts.lean` records it as all that is left of the row
`hullHypEmbeddedConeOff`.

**It is false**, and this module proves it.  So that reduction is vacuous, and
the debt cannot be closed along it.

## The obstruction, in three letters

`GGT.RelGenSet.relBall lam n` measures `d̂_lam` — the length of a shortest word
from `1` to `h` in `Γ(G, X ⊔ ⨆H)` traversing no edge of `Γ_{H lam}`.  The
avoidance condition `GGT.AvoidsFrom` forbids a `lam`-letter only at a vertex
lying *in* `H lam`.  So if some `a ∈ X` is **not** in `H lam`, the word

    [base a, comp lam k, base a]

reads a `lam`-letter at the vertex `a`, which is legal, and spells `a k a`.
Whenever `a k a` lands back in `H lam` this puts it in the ball of radius
three, whatever `k` is: `mem_relBall_three_of_base_conj`.

At `H lam = ⟨a²⟩` that happens for every `k`, since `a · a^{2m} · a = a^{2m+2}`.
The whole subgroup collapses into `relBall lam 3`, which is therefore infinite,
and clause (b) of `GGT.RelGenSet.IsHyperbolicallyEmbedded` fails:
`infinite_relBall_three_of_sq`.

This is not an artefact of the formalization.  It is
Dahmani--Guirardel--Osin's Proposition 4.33 — a hyperbolically embedded family
is almost malnormal — biting at `g = a`: the conjugate `⟨a²⟩^a` is `⟨a²⟩`
itself, infinite, while `a ∉ ⟨a²⟩`.  `GGT/DGOProposition433Ball.lean` already
says as much in words for the `mu = lam`, `f ∈ H_lam` case.

## The model

`HullSC.freeHullGeneratingSet` is Hull's data for a free group of rank two: the
basis alphabet, hyperbolic at `δ = 0` because the Cayley graph is a tree,
acylindrical because the alphabet is finite, non-elementary because two distinct
basis letters are independent loxodromics.  All three proofs are
`GGT/HyperbolicFreeGroupAH.lean`'s and are used rather than restated.

Against it, `HullSC.not_zpowersConeOffEmbedding` refutes the clause with the
pair `(a², b)`, where `a = FreeGroup.of 0` and `b = FreeGroup.of 1`.  Both are
loxodromic — a positive power of a loxodromic is loxodromic — and independent,
since independence quantifies over all integer exponents and the exponents of
`a²` are a subfamily of those of `a`.  So the hypothesis applies and its
conclusion fails.

## What survives

`HullSC.ExistsHypEmbeddedConeOff₂` itself is untouched: its family `K` is
existentially quantified, so `K b = E(g b)` is still available and the four
cheap clauses of the reduction can be recovered at
`elementaryClosure (g b) ⊓ N`, where the containment in `N` is `inf_le_right`
and Hull's (W4) still follows from independence.  What the refutation removes is
the claim that the *cyclic* choice costs nothing: almost malnormality forces
`elementaryClosure (g b) = zpowers (g b)` for any pair the reduction could be
applied to, which is a real extra obligation on the choice of the two
loxodromics.
-/

namespace GroupApproximation

universe u v w

namespace GGT

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

/-! ## The three-letter escape -/

/-- **A letter of the base outside the family carries the whole family into the
ball of radius three.**

If `a` is a letter of `X` that does not lie in `H lam`, then reading `a`, then a
`lam`-letter `k`, then `a` again is admissible: the middle letter is read at the
vertex `a`, which is outside `H lam`, so it traverses no edge of `Γ_{H lam}`.
The word spells `a k a`, so whenever that lands back in `H lam` its relative
distance to `1` is at most three.

This is the mechanism behind Dahmani--Guirardel--Osin's Proposition 4.33: a
family that is not almost malnormal has an unbounded relative ball. -/
theorem mem_relBall_three_of_base_conj {G : Type u} [Group G] {Λ : Type w}
    (D : RelGenSet G Λ) (lam : Λ) {a k : G} (ha : a ∈ D.base)
    (hna : a ∉ D.fam lam) (hk : k ∈ D.fam lam) (hak : a * k * a ∈ D.fam lam) :
    a * k * a ∈ D.relBall lam 3 := by
  refine ⟨hak, [RelLetter.base a, RelLetter.comp lam k, RelLetter.base a],
    ?_, ?_, ?_, ?_⟩
  · intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact ha
    rcases List.mem_cons.mp hz with rfl | hz
    · exact hk
    rcases List.mem_cons.mp hz with rfl | hz
    · exact ha
    · simp at hz
  · show (([RelLetter.base a, RelLetter.comp lam k,
        RelLetter.base a]).map RelLetter.val).prod = a * k * a
    show a * (k * (a * 1)) = a * k * a
    rw [mul_one, ← mul_assoc]
  · refine ⟨?_, ?_, ?_, trivial⟩
    · rintro ⟨hc, -⟩
      exact hc
    · show ¬ (RelLetter.IsCompOf lam (RelLetter.comp lam k) ∧
        (1 : G) * a ∈ D.fam lam)
      rintro ⟨-, hv⟩
      rw [one_mul] at hv
      exact hna hv
    · rintro ⟨hc, -⟩
      exact hc
  · simp

/-! ## The square of a loxodromic element -/

/-- **The relative ball of radius three is infinite at a proper power.**

With `H lam = ⟨a²⟩` and `a` a letter of the base, every element `a^{2m+2}` of
the family is `a · a^{2m} · a`, so `mem_relBall_three_of_base_conj` puts all of
them in the ball of radius three; loxodromy of `a` makes them pairwise distinct,
and also puts `a` itself outside `⟨a²⟩`, which is what makes the middle letter
legal. -/
theorem infinite_relBall_three_of_sq {G : Type u} [Group G] {Λ : Type w}
    {X : Type v} [PseudoMetricSpace X] [MulAction G X]
    (D : RelGenSet G Λ) (lam : Λ) {a : G} {x : X} (ha : a ∈ D.base)
    (hlox : IsLoxodromic a x)
    (hfam : D.fam lam = Subgroup.zpowers (a ^ (2 : ℕ))) :
    (D.relBall lam 3).Infinite := by
  have hinj : Function.Injective (fun n : ℤ => a ^ n) :=
    injective_zpow_iff_not_isOfFinOrder.mpr (not_isOfFinOrder_of_isLoxodromic hlox)
  have hzp : ∀ n : ℤ, (a ^ (2 : ℕ)) ^ n = a ^ (2 * n) := by
    intro n
    have h2 : a ^ (2 : ℕ) = a ^ (2 : ℤ) := by
      rw [show ((2 : ℤ)) = ((2 : ℕ) : ℤ) from by norm_num, zpow_natCast]
    rw [h2, ← zpow_mul]
  have hna : a ∉ D.fam lam := by
    rw [hfam]
    intro hmem
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hmem
    rw [hzp m] at hm
    have h1 : a ^ (2 * m) = a ^ (1 : ℤ) := by rw [hm, zpow_one]
    have h2 : 2 * m = (1 : ℤ) := hinj h1
    omega
  have hsq : ∀ m : ℤ, a * a ^ (2 * m) * a = a ^ (2 * m + 2) := by
    intro m
    have h : (2 * m + 2 : ℤ) = 1 + 2 * m + 1 := by ring
    rw [h, zpow_add, zpow_add, zpow_one]
  have hmem0 : ∀ m : ℤ, a ^ (2 * m) ∈ D.fam lam := by
    intro m
    rw [hfam]
    exact Subgroup.mem_zpowers_iff.mpr ⟨m, hzp m⟩
  have hmem2 : ∀ m : ℤ, a ^ (2 * m + 2) ∈ D.fam lam := by
    intro m
    rw [hfam]
    refine Subgroup.mem_zpowers_iff.mpr ⟨m + 1, ?_⟩
    rw [hzp (m + 1), show (2 * (m + 1) : ℤ) = 2 * m + 2 from by ring]
  refine Set.infinite_of_injective_forall_mem
    (f := fun m : ℤ => a ^ (2 * m + 2)) ?_ ?_
  · intro p q hpq
    have hpq' : a ^ (2 * p + 2) = a ^ (2 * q + 2) := hpq
    have h2 : 2 * p + 2 = 2 * q + 2 := hinj hpq'
    omega
  · intro m
    have hkey := mem_relBall_three_of_base_conj D lam ha hna (hmem0 m)
      (by rw [hsq m]; exact hmem2 m)
    rw [hsq m] at hkey
    exact hkey

/-- **A family whose `lam`-th member is generated by the square of a letter of
the base is not hyperbolically embedded.**  Clause (b) fails at radius three. -/
theorem not_isHyperbolicallyEmbedded_of_sq {G : Type u} [Group G] {Λ : Type w}
    {X : Type v} [PseudoMetricSpace X] [MulAction G X]
    (D : RelGenSet G Λ) (lam : Λ) {a : G} {x : X} (ha : a ∈ D.base)
    (hlox : IsLoxodromic a x)
    (hfam : D.fam lam = Subgroup.zpowers (a ^ (2 : ℕ))) :
    ¬ D.IsHyperbolicallyEmbedded := fun h =>
  infinite_relBall_three_of_sq D lam ha hlox hfam (h.locallyFinite lam 3)

end GGT

namespace HullSC

open GroupApproximation.GGT
open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

/-! ## The cone-off form -/

/-- **The cone-off along a family containing the square of a letter of the
alphabet is never hyperbolically embedded.**  The base of `coneOffFamily A K` is
`A.carrier` and its family is `K`, so this is `not_isHyperbolicallyEmbedded_of_sq`
read at that relative generating set. -/
theorem not_isHyperbolicallyEmbedded_coneOffFamily_of_sq {G : Type u} [Group G]
    {Λ : Type w} {X : Type v} [PseudoMetricSpace X] [MulAction G X]
    (A : Alphabet G) (K : Λ → Subgroup G) (lam : Λ) {a : G} {x : X}
    (ha : a ∈ A.carrier) (hlox : IsLoxodromic a x)
    (hK : K lam = Subgroup.zpowers (a ^ (2 : ℕ))) :
    ¬ (coneOffFamily A K).IsHyperbolicallyEmbedded :=
  GGT.not_isHyperbolicallyEmbedded_of_sq (coneOffFamily A K) lam ha hlox hK

/-! ## Hull's data for a free group of rank two -/

/-- `Γ(F₂, A)` is `0`-hyperbolic: it is a tree. -/
theorem free_hyperbolic :
    IsHyperbolicSpace 0 (Cayley (GGT.freeGroupAlphabet (Fin 2))) :=
  GGT.isHyperbolicSpace_zero_cayley Hyperbolic.isTreeLike_freeAlphabet

/-- The translation action of `F₂` on `Γ(F₂, A)` is acylindrical: the alphabet
is finite, so the action is proper. -/
theorem free_acylindrical :
    IsAcylindrical (FreeGroup (Fin 2))
      (Cayley (GGT.freeGroupAlphabet (Fin 2))) := by
  have hfin : (Hyperbolic.freeAlphabet (Fin 2)).Finite := Set.finite_range _
  exact GGT.isAcylindrical_cayley_of_finite (GGT.freeGroupAlphabet (Fin 2)) hfin

/-- `F₂` acts non-elementarily on `Γ(F₂, A)`: the two basis letters are
independent loxodromics. -/
theorem free_nonElementary :
    ActsNonElementarily (⊤ : Subgroup (FreeGroup (Fin 2)))
      (Cayley.base (GGT.freeGroupAlphabet (Fin 2))) :=
  ⟨FreeGroup.of 0, Subgroup.mem_top _, FreeGroup.of 1, Subgroup.mem_top _,
    GGT.isLoxodromic_of_basis (a := (0 : Fin 2)) (b := (1 : Fin 2)) (by decide),
    GGT.isLoxodromic_of_basis (a := (1 : Fin 2)) (b := (0 : Fin 2)) (by decide),
    GGT.independent_of_basis (a := (0 : Fin 2)) (b := (1 : Fin 2)) (by decide)⟩

/-- **Hull's Theorem 3.12 data for a free group of rank two.**  Every field is a
theorem of `GGT/HyperbolicFreeGroupAH.lean`; nothing new is proved here.  This
is the model the refutation below runs on. -/
def freeHullGeneratingSet : HullGeneratingSet (FreeGroup (Fin 2)) where
  alphabet := GGT.freeGroupAlphabet (Fin 2)
  delta := 0
  hyperbolic := free_hyperbolic
  acylindrical := free_acylindrical
  nonElementary := free_nonElementary

/-! ## The refuted clause -/

/-- **The hypothesis of `existsHypEmbeddedConeOff₂_of_zpowers_forall`, named.**

`GGT/HullSCConeOffCyclicReduction.lean` states it inline as a binder and its
docstring calls it "the sharpest form of what Hull's §5 for a pair still owes".
Naming it is what lets `not_zpowersConeOffEmbedding` refute it. -/
def ZpowersConeOffEmbedding : Prop :=
  ∀ {G : Type u} [Group G] (A : HullGeneratingSet G) (g : Bool → G),
    (∀ b : Bool, IsLoxodromic (g b) (Cayley.base A.alphabet)) →
      Independent (g false) (g true) (Cayley.base A.alphabet) →
        (coneOffFamily A.alphabet
          (fun b => Subgroup.zpowers (g b))).IsHyperbolicallyEmbedded

/-- The named clause is exactly the binder the cyclic reduction consumes. -/
theorem existsHypEmbeddedConeOff₂_of_zpowersConeOffEmbedding
    (h : ZpowersConeOffEmbedding.{u}) : ExistsHypEmbeddedConeOff₂.{u} :=
  existsHypEmbeddedConeOff₂_of_zpowers_forall h

/-- **The clause is false.**

At `G = F₂` with Hull's own alphabet, `a²` and `b` are independent loxodromics,
but the cone-off along `⟨a²⟩` and `⟨b⟩` is not hyperbolically embedded: `a` is a
letter of the alphabet lying outside `⟨a²⟩`, so the three-letter word
`a · a^{2m} · a` puts every element of `⟨a²⟩` in the relative ball of radius
three.

So `existsHypEmbeddedConeOff₂_of_zpowers_forall` is vacuous, and the row
`Manuscript.NonMF.TorsionFree.hullHypEmbeddedConeOff` does not reduce to it. -/
theorem not_zpowersConeOffEmbedding : ¬ ZpowersConeOffEmbedding.{0} := by
  intro h
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  have hloxa : IsLoxodromic (FreeGroup.of (0 : Fin 2))
      (Cayley.base freeHullGeneratingSet.alphabet) :=
    GGT.isLoxodromic_of_basis (a := (0 : Fin 2)) (b := (1 : Fin 2)) h01
  have hzp : ∀ n : ℤ, (FreeGroup.of (0 : Fin 2) ^ (2 : ℕ)) ^ n
      = FreeGroup.of (0 : Fin 2) ^ (2 * n) := by
    intro n
    have h2 : FreeGroup.of (0 : Fin 2) ^ (2 : ℕ)
        = FreeGroup.of (0 : Fin 2) ^ (2 : ℤ) := by
      rw [show ((2 : ℤ)) = ((2 : ℕ) : ℤ) from by norm_num, zpow_natCast]
    rw [h2, ← zpow_mul]
  have hlox : ∀ b : Bool,
      IsLoxodromic
        (bif b then FreeGroup.of (1 : Fin 2)
          else FreeGroup.of (0 : Fin 2) ^ (2 : ℕ))
        (Cayley.base freeHullGeneratingSet.alphabet) := by
    intro b
    cases b
    · show IsLoxodromic (FreeGroup.of (0 : Fin 2) ^ (2 : ℕ))
        (Cayley.base freeHullGeneratingSet.alphabet)
      exact isLoxodromic_pow hloxa (by norm_num)
    · show IsLoxodromic (FreeGroup.of (1 : Fin 2))
        (Cayley.base freeHullGeneratingSet.alphabet)
      exact GGT.isLoxodromic_of_basis (a := (1 : Fin 2)) (b := (0 : Fin 2)) h10
  have hind : Independent (FreeGroup.of (0 : Fin 2) ^ (2 : ℕ))
      (FreeGroup.of (1 : Fin 2))
      (Cayley.base freeHullGeneratingSet.alphabet) := by
    obtain ⟨C, hC⟩ := GGT.independent_of_basis (a := (0 : Fin 2))
      (b := (1 : Fin 2)) h01
    refine ⟨C, ?_⟩
    intro n m
    have hstep := hC (2 * n) m
    rw [← hzp n] at hstep
    exact hstep
  have hbase : FreeGroup.of (0 : Fin 2) ∈ freeHullGeneratingSet.alphabet.carrier :=
    Hyperbolic.letterOf_mem ((0 : Fin 2), true)
  have hemb := h freeHullGeneratingSet
    (fun c : Bool => bif c then FreeGroup.of (1 : Fin 2)
      else FreeGroup.of (0 : Fin 2) ^ (2 : ℕ)) hlox hind
  exact not_isHyperbolicallyEmbedded_coneOffFamily_of_sq
    freeHullGeneratingSet.alphabet _ false hbase hloxa rfl hemb

end HullSC
end GroupApproximation
