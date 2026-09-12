import GroupApproximation.CharClass.ParityPSplitStepD
import GroupApproximation.CharClass.LIXStepDGenRealEven

/-!
# The splitting principle over `K`, layer 1: from splitting data to `HasSplittingP`

Lane `lix-evenside`, prefix `CharClass/ChernSplittingOf*` (lead's ruling of 2026-09-11).

`ParityP.HasSplittingP p γ PH κ` is the splitting principle in the form Step D mod `p`
consumes: an injective ring map from the Chern classes into a commutative ring carrying a split
family of roots, with the reduced powers intertwined and `P(y) = y + κ·y^p` on the roots.
At odd `p` the cohomology ring `TotalHOf K X` is only graded-commutative, so both rings are
**even parts** (`Gen.evenPart`, `lix-evenside-n`), which are commutative.

This file produces `HasSplittingP` from two inputs of different kinds:

* `SplittingDataOf K N F r γ` — the geometry: a map `F ⟶ N` injective on cohomology and degree-two
  classes on `F` whose elementary symmetric functions are the pulled-back Chern classes;
* the reduced powers on `N` and `F`, as additive maps preserving evenness, with `P⁰ = id`, the
  Cartan formula on `F`, `P¹ h = m·h^p` and `P^{≥2} h = 0` on degree-two classes, and naturality
  along the map.  These are the export of the odd-primary operations.

Nothing here depends on the sign convention for the roots: a root may be replaced by its
negative, since `P¹(−h) = m·(−h)^p` at odd `p` and signs are invisible at `p = 2`.

## Main results

* `SplittingDataOf` — the geometric input over `K`.
* `evenCoe` — the inclusion of the even part as a ring hom.
* `SplittingDataOf.powerData` — the `PowerData` of the roots on the even part of `F`.
* `hasSplittingP_of_splittingDataOf` — **the producer**.
* `ParityP.HasSplittingP.elim` — the destructuring form the rank-`n` bridge consumes.
-/

set_option autoImplicit false

namespace GroupApproximation.CharClass

open CategoryTheory ParityP

noncomputable section

/-! ## 1. The inclusion of the even part -/

/-- The inclusion of the even part, as a ring homomorphism with definitional equations. -/
def evenCoe (K : Type) [CommRing K] (X : TopCat.{0}) : Gen.evenPart K X →+* TotalHOf K X where
  toFun a := a
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem evenCoe_apply (K : Type) [CommRing K] (X : TopCat.{0}) (a : Gen.evenPart K X) :
    evenCoe K X a = (a : TotalHOf K X) := rfl

theorem evenCoe_injective (K : Type) [CommRing K] (X : TopCat.{0}) :
    Function.Injective (evenCoe K X) :=
  fun _ _ h => Subtype.ext h

/-! ## 2. The geometric input -/

/-- **Splitting data over `K`.**  `F` is the flag space of a bundle over `N`, `root l` its roots
in degree two, and `chern_split` says that the pullback of `γ k` is the `k`-th elementary
symmetric function of the roots.  Both sides live in the even parts, which are commutative;
the whole ring `TotalHOf K F` is not, so `esymmOn` cannot be formed there. -/
structure SplittingDataOf (K : Type) [CommRing K] (N F : TopCat.{0}) (r : ℕ)
    (γ : ℕ → Gen.evenPart K N) where
  /-- The flag bundle projection. -/
  proj : F ⟶ N
  /-- The roots, of cohomological degree two. -/
  root : ℕ → TotalPieceOf K F 2
  /-- The pullback is injective on cohomology. -/
  pull_injective : Function.Injective (TotalHOf.map K proj)
  /-- Whitney on the flag bundle: `π^* γ_k = e_k(roots)`, in the even part of `F`. -/
  chern_split : ∀ k : ℕ,
    Gen.evenMap K proj (γ k)
      = esymmOn (Finset.range r)
          (fun l => (⟨TotalHOf.of K F 2 (root l), TotalHOf.isEven_of K F even_two (root l)⟩ :
            Gen.evenPart K F)) k

namespace SplittingDataOf

variable {K : Type} [CommRing K] {N F : TopCat.{0}} {r : ℕ} {γ : ℕ → Gen.evenPart K N}
  (S : SplittingDataOf K N F r γ)

/-- The roots, as elements of the even part of `F`. -/
def evenRoot (l : ℕ) : Gen.evenPart K F :=
  ⟨TotalHOf.of K F 2 (S.root l), TotalHOf.isEven_of K F even_two (S.root l)⟩

/-- **The `PowerData` of the roots** on the even part of `F`. -/
def powerData {p : ℕ} (PF : ℕ → TotalHOf K F →+ TotalHOf K F)
    (hPF : ∀ (i : ℕ) (x : TotalHOf K F), TotalHOf.IsEven x → TotalHOf.IsEven (PF i x))
    (hzero : ∀ x : TotalHOf K F, PF 0 x = x)
    (hcartan : ∀ (i : ℕ) (u v : TotalHOf K F),
      PF i (u * v) = ∑ j ∈ Finset.range (i + 1), PF j u * PF (i - j) v)
    (m : ℤ)
    (hone : ∀ h : TotalPieceOf K F 2,
      PF 1 (TotalHOf.of K F 2 h) = (m : TotalHOf K F) * TotalHOf.of K F 2 h ^ p)
    (hhigh : ∀ (h : TotalPieceOf K F 2) (j : ℕ), 2 ≤ j → PF j (TotalHOf.of K F 2 h) = 0) :
    PowerData ℕ (Gen.evenPart K F) p where
  P := fun i => Gen.evenRestrictAdd (PF i) (hPF i)
  p_zero_apply := fun a => Subtype.ext (hzero a)
  cartan := fun n u v => by
    apply evenCoe_injective K F
    rw [map_sum]
    refine (hcartan n (u : TotalHOf K F) v).trans (Finset.sum_congr rfl fun j _ => ?_)
    exact (map_mul (evenCoe K F) _ _).symm
  s := Finset.range r
  y := S.evenRoot
  κ := (m : Gen.evenPart K F)
  p_y_one := fun k => by
    apply evenCoe_injective K F
    exact hone (S.root k)
  p_y_high := fun k j hj => by
    apply evenCoe_injective K F
    exact hhigh (S.root k) j hj

end SplittingDataOf

/-! ## 3. The producer -/

/-- **The splitting principle over `K`, in the form Step D mod `p` consumes.**  Splitting data for
`γ` and reduced powers on `N` and `F` compatible with the projection give `HasSplittingP` for the
even Chern classes, with the reduced powers of `N` restricted to the even part. -/
theorem hasSplittingP_of_splittingDataOf {K : Type} [CommRing K] {p : ℕ} {N F : TopCat.{0}}
    {r : ℕ} {γ : ℕ → Gen.evenPart K N} (S : SplittingDataOf K N F r γ)
    (PN : ℕ → TotalHOf K N →+ TotalHOf K N)
    (hPN : ∀ (i : ℕ) (x : TotalHOf K N), TotalHOf.IsEven x → TotalHOf.IsEven (PN i x))
    (PF : ℕ → TotalHOf K F →+ TotalHOf K F)
    (hPF : ∀ (i : ℕ) (x : TotalHOf K F), TotalHOf.IsEven x → TotalHOf.IsEven (PF i x))
    (hzero : ∀ x : TotalHOf K F, PF 0 x = x)
    (hcartan : ∀ (i : ℕ) (u v : TotalHOf K F),
      PF i (u * v) = ∑ j ∈ Finset.range (i + 1), PF j u * PF (i - j) v)
    (m : ℤ)
    (hone : ∀ h : TotalPieceOf K F 2,
      PF 1 (TotalHOf.of K F 2 h) = (m : TotalHOf K F) * TotalHOf.of K F 2 h ^ p)
    (hhigh : ∀ (h : TotalPieceOf K F 2) (j : ℕ), 2 ≤ j → PF j (TotalHOf.of K F 2 h) = 0)
    (hnat : ∀ (i : ℕ) (x : TotalHOf K N),
      PF i (TotalHOf.map K S.proj x) = TotalHOf.map K S.proj (PN i x)) :
    HasSplittingP p γ (fun i => Gen.evenRestrictAdd (PN i) (hPN i)) m := by
  refine ⟨Gen.evenPart K F, inferInstance, ℕ, inferInstance,
    S.powerData PF hPF hzero hcartan m hone hhigh, Gen.evenMap K S.proj, ?_, ?_, ?_, rfl⟩
  · intro a b hab
    exact Subtype.ext (S.pull_injective (congrArg Subtype.val hab))
  · intro k
    exact S.chern_split k
  · intro i x
    apply evenCoe_injective K F
    exact (hnat i (x : TotalHOf K N)).symm

end

/-- **Destructuring `HasSplittingP`**, into the components the rank-`n` bridge
(`Gen.realWu_of_splitting`) takes. -/
theorem ParityP.HasSplittingP.elim {p : ℕ} {H : Type} [CommRing H] {γ : ℕ → H}
    {PH : ℕ → H →+ H} {κ : ℤ} (h : HasSplittingP p γ PH κ) {C : Prop}
    (hC : ∀ (A : Type) [CommRing A] (σ : Type) [DecidableEq σ] (D : PowerData σ A p)
      (ρ : H →+* A), Function.Injective ρ → (∀ k, ρ (γ k) = D.gamma k) →
        (∀ (i : ℕ) (x : H), ρ (PH i x) = D.P i (ρ x)) → D.κ = (κ : A) → C) : C := by
  obtain ⟨A, _, σ, _, D, ρ, h1, h2, h3, h4⟩ := h
  exact hC A σ D ρ h1 h2 h3 h4

end GroupApproximation.CharClass
