import GroupApproximation.CharClass.ParityInstance
import GroupApproximation.CharClass.SteenrodCartanTotal
import GroupApproximation.CharClass.WuDiagonal

/-!
# The splitting principle as one input, and `hwu` for free

`ParityInstance.lean` leaves five hypotheses on the endpoint of the even side of
Lemma 2.  One of them, `hwu`, is the diagonal Wu relation for the mod-2 Chern
classes of `W` over `N`.  This file removes it from the interface: it builds the
`SqData` of `WuDiagonal.lean` on the flag total space, proves (Wu-diag) there,
and pushes it down to `N` along the injective pullback.  What is left is **one**
bundled input from `cc-projective`, the structure `SplittingData`, plus the
Cartan formula.

## `SplittingData`

```text
proj           : F ⟶ N                     the flag bundle projection
root           : ℕ → Hmod2 F 2             the Chern roots, in degree two
pull_injective : Function.Injective (TotalH.map proj)
sq_one_root    : ∀ l, Sq 1 (root l) = 0
chern_split    : ∀ k, TotalH.map proj (γ k) = e_k(root)
```

`sq_one_root` is the only genuinely Steenrod-flavoured input: `Sq^1` kills a
degree-two class that is the reduction of an integral one, which for a line class
is `H³(ℂP^{K-1}; F₂) = 0` plus naturality.  Everything else about the roots —
`Sq^0 = id`, `Sq^2 ℓ = ℓ²`, `Sq^j ℓ = 0` for `j ≥ 3` — is proved here from
`SteenrodTotal`, because a class of the form `TotalH.of F 2 β` carries its degree
with it.

## The Cartan formula, once

`CartanTotal` is `cc-steenrod`'s `Steenrod.CartanOf` quantified over the space, so
a single hypothesis discharges the Cartan field both at `N` (for
`ParityData.cartanH`) and at the flag space `F` (for `SqData.cartan`), through
`Steenrod.SqH_mul_of_cartanOf`.

## Degreewise to ring-level injectivity

`cc-projective`'s Leray–Hirsch gives injectivity of `pull π n` one degree at a
time (`LerayHirschGraded.pull_injective`).  `totalH_map_injective` turns that into
injectivity of the ring map `TotalH.map π`, which is what
`SplittingData.pull_injective` asks for.
-/

set_option autoImplicit false

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation
namespace CharClass
namespace Wu

noncomputable section

/-! ## 1. The Cartan formula, quantified over the space -/

/-- `cc-cartan`'s Cartan formula for every space at once.  One hypothesis of this
type discharges the Cartan field wherever it is needed. -/
def CartanTotal : Prop := ∀ X : TopCat.{0}, Steenrod.CartanOf X

/-- The Cartan formula in the shape `ParityData.cartanH` and `SqData.cartan` ask
for, at any space. -/
theorem cartanH_of (hC : CartanTotal) (X : TopCat.{0}) (n : ℕ) (u v : TotalH X) :
    Steenrod.SqH X n (u * v)
      = ∑ i ∈ Finset.range (n + 1), Steenrod.SqH X i u * Steenrod.SqH X (n - i) v :=
  Steenrod.SqH_mul_of_cartanOf (hC X) n u v

/-! ## 2. Degreewise injectivity gives ring-level injectivity -/

theorem component_of_ne {X : TopCat.{0}} {n m : ℕ} (h : n ≠ m) (a : TotalPiece X m) :
    TotalH.component X n (TotalH.of X m a) = 0 :=
  DirectSum.of_eq_of_ne m n a h

theorem totalH_component_map {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) (c : TotalH Y) :
    TotalH.component X n (TotalH.map f c) = pull f n (TotalH.component Y n c) := by
  induction c using DirectSum.induction_on with
  | zero => simp only [map_zero, pull_zero]
  | of m a =>
    show TotalH.component X n (TotalH.map f (TotalH.of Y m a))
      = pull f n (TotalH.component Y n (TotalH.of Y m a))
    rw [TotalH.map_of]
    rcases eq_or_ne n m with rfl | hnm
    · rw [TotalH.component_of, TotalH.component_of]
    · rw [component_of_ne hnm, component_of_ne hnm, pull_zero]
  | add u v hu hv => simp only [map_add, pull_add, hu, hv]

/-- **`cc-projective`'s Leray–Hirsch injectivity, on the ring.**  Degreewise
injectivity of `pull π n` gives injectivity of the ring map `TotalH.map π`. -/
theorem totalH_map_injective {X Y : TopCat.{0}} (f : X ⟶ Y)
    (h : ∀ n : ℕ, Function.Injective (pull f n)) :
    Function.Injective (TotalH.map f) := by
  intro c c' hcc
  ext n
  refine h n ?_
  show pull f n (TotalH.component Y n c) = pull f n (TotalH.component Y n c')
  rw [← totalH_component_map, ← totalH_component_map, hcc]

/-! ## 3. The splitting principle, as one bundled input -/

/-- **The splitting principle for `γ`, as a single input from `cc-projective`.**
`F` is the flag total space of the bundle `W` over `N`, `root l` its `r` Chern
roots in degree two, and `chern_split` says that the pullback of `γ_k` is the
`k`-th elementary symmetric function of the roots — that is, Whitney applied to
`cc-bundle`'s `flag_decomposition`. -/
structure SplittingData (N F : TopCat.{0}) (r : ℕ) (γ : ℕ → TotalH N) where
  /-- The flag bundle projection. -/
  proj : F ⟶ N
  /-- The Chern roots, of cohomological degree two. -/
  root : ℕ → Hmod2 F 2
  /-- Leray–Hirsch: the pullback is injective on cohomology.  Obtainable from the
  degreewise statement by `totalH_map_injective`. -/
  pull_injective : Function.Injective (TotalH.map proj)
  /-- `Sq¹` kills a degree-two class that is the reduction of an integral one;
  for a line class this is `H³(ℂP^{K-1}; F₂) = 0` plus naturality. -/
  sq_one_root : ∀ l : ℕ, Sq 1 (root l) = 0
  /-- Whitney on the flag bundle: `π^* γ_k = e_k(roots)`. -/
  chern_split : ∀ k : ℕ,
    TotalH.map proj (γ k)
      = esymmOn (Finset.range r) (fun l => TotalH.of F 2 (root l)) k

namespace SplittingData

/-- **The `SqData` of the flag bundle.**  Only `cartan` comes from outside; the
three root laws are proved from `SteenrodTotal`, because `TotalH.of F 2 β`
carries its degree. -/
def sqData {N F : TopCat.{0}} {r : ℕ} {γ : ℕ → TotalH N} (S : SplittingData N F r γ)
    (hC : CartanTotal) : SqData ℕ (TotalH F) where
  two_eq_zero := totalH_two_eq_zero F
  Sq := Steenrod.SqH F
  sq_zero_apply := Steenrod.SqH_zero_apply F
  cartan := cartanH_of hC F
  s := Finset.range r
  y := fun l => TotalH.of F 2 (S.root l)
  sq_y_one := fun l => by
    show Steenrod.SqH F 1 (TotalH.of F 2 (S.root l)) = 0
    rw [Steenrod.SqH_of, S.sq_one_root l, map_zero]
  sq_y_two := fun l => by
    show Steenrod.SqH F 2 (TotalH.of F 2 (S.root l)) = TotalH.of F 2 (S.root l) ^ 2
    rw [pow_two]
    exact Steenrod.SqH_of_self F 2 (S.root l)
  sq_y_high := fun l n hn => Steenrod.SqH_of_eq_zero_of_lt F n 2 (by omega) (S.root l)

/-- **(Wu-diag) for `γ` over `N`.**  Proved on the flag total space by
`SqData.wu_diagonal` and pushed down by injectivity of the pullback.  This is
exactly the `hwu` hypothesis of `Wu.parityData_of`. -/
theorem wu {N F : TopCat.{0}} {r : ℕ} {γ : ℕ → TotalH N} (S : SplittingData N F r γ)
    (hC : CartanTotal) (i : ℕ) :
    Steenrod.SqH N (2 * i) (γ (i + 1))
      = ∑ j ∈ Finset.range (i + 1), γ (i - j) * γ (i + 1 + j) := by
  have hD : Steenrod.SqH F (2 * i)
        (esymmOn (Finset.range r) (fun l => TotalH.of F 2 (S.root l)) (i + 1))
      = ∑ j ∈ Finset.range (i + 1),
          esymmOn (Finset.range r) (fun l => TotalH.of F 2 (S.root l)) (i - j)
            * esymmOn (Finset.range r) (fun l => TotalH.of F 2 (S.root l)) (i + 1 + j) :=
    (S.sqData hC).wu_diagonal i
  refine S.pull_injective ?_
  rw [← Steenrod.SqH_map, S.chern_split (i + 1), hD, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, S.chern_split, S.chern_split]

end SplittingData

/-- **The splitting principle with the flag space and its rank hidden.**  A
consumer whose record does not otherwise mention the flag bundle wants a single
`Prop`-valued field, not two extra type parameters; this is that field. -/
def HasSplitting (N : TopCat.{0}) (γ : ℕ → TotalH N) : Prop :=
  ∃ (F : TopCat.{0}) (r : ℕ), Nonempty (SplittingData N F r γ)

/-- (Wu-diag) from the existentially quantified splitting principle. -/
theorem HasSplitting.wu {N : TopCat.{0}} {γ : ℕ → TotalH N} (hS : HasSplitting N γ)
    (hC : CartanTotal) (i : ℕ) :
    Steenrod.SqH N (2 * i) (γ (i + 1))
      = ∑ j ∈ Finset.range (i + 1), γ (i - j) * γ (i + 1 + j) := by
  obtain ⟨F, r, ⟨S⟩⟩ := hS
  exact S.wu hC i


/-! ## 4. The endpoint with `hwu` and `hcartan` collapsed -/

/-- **Lemma 2, the even half, with the Wu relation supplied by the splitting
principle.**  Four hypotheses remain: the Cartan formula (`cc-cartan`), the
two-sphere Künneth injectivity and the Künneth decomposition of the Chern classes
with its degree bookkeeping (`cc-cohom-api`), and the splitting principle
(`cc-projective`).  Rank-free. -/
theorem gamma_top_eq_zero_of_splitting
    {N Y S₁ S₅ F : TopCat.{0}} {r : ℕ}
    (p : N ⟶ Y) (q₁ : N ⟶ S₁) (q₅ : N ⟶ S₅)
    (hS₁ : HasSphereCohomology S₁ 1) (hS₅ : HasSphereCohomology S₅ 5)
    (σ₁ : Hmod2 S₁ 1) (σ₅ : Hmod2 S₅ 5)
    (γ : ℕ → TotalH N) (a b : ℕ → TotalH Y)
    (hC : CartanTotal)
    (htx_inj : ∀ u v : TotalH Y,
      TotalH.map p u + tClass q₁ σ₁ * xClass q₅ σ₅ * TotalH.map p v = 0 → v = 0)
    (hγ : ∀ k : ℕ,
      γ k = TotalH.map p (a k) + tClass q₁ σ₁ * xClass q₅ σ₅ * TotalH.map p (b k))
    (hsq_b : ∀ k j : ℕ, 2 * k < j + 6 → Steenrod.SqH Y j (b k) = 0)
    (S : SplittingData N F r γ)
    {J : Type} (u : Finset J) (h : J → TotalH Y) (d : J → ℕ)
    (hd : ∀ j ∈ u, Even (d j))
    (hslice : ∀ q : ℕ, a q = (sliceClass u h d).coeff q) :
    γ ((∑ j ∈ u, d j) + 3) = 0 :=
  gamma_top_eq_zero_of_slice_totalH p q₁ q₅ hS₁ hS₅ σ₁ σ₅ γ a b (cartanH_of hC N)
    htx_inj hγ hsq_b (S.wu hC) u h d hd hslice

/-- **Lemma 2, the even half, from the `Prop`-valued splitting principle.**  Same
as `gamma_top_eq_zero_of_splitting` with the flag space and rank hidden, so that
`hsplit` is one field of a record rather than two type parameters plus a field. -/
theorem gamma_top_eq_zero_of_hasSplitting
    {N Y S₁ S₅ : TopCat.{0}}
    (p : N ⟶ Y) (q₁ : N ⟶ S₁) (q₅ : N ⟶ S₅)
    (hS₁ : HasSphereCohomology S₁ 1) (hS₅ : HasSphereCohomology S₅ 5)
    (σ₁ : Hmod2 S₁ 1) (σ₅ : Hmod2 S₅ 5)
    (γ : ℕ → TotalH N) (a b : ℕ → TotalH Y)
    (hC : CartanTotal)
    (htx_inj : ∀ u v : TotalH Y,
      TotalH.map p u + tClass q₁ σ₁ * xClass q₅ σ₅ * TotalH.map p v = 0 → v = 0)
    (hγ : ∀ k : ℕ,
      γ k = TotalH.map p (a k) + tClass q₁ σ₁ * xClass q₅ σ₅ * TotalH.map p (b k))
    (hsq_b : ∀ k j : ℕ, 2 * k < j + 6 → Steenrod.SqH Y j (b k) = 0)
    (hsplit : HasSplitting N γ)
    {J : Type} (u : Finset J) (h : J → TotalH Y) (d : J → ℕ)
    (hd : ∀ j ∈ u, Even (d j))
    (hslice : ∀ q : ℕ, a q = (sliceClass u h d).coeff q) :
    γ ((∑ j ∈ u, d j) + 3) = 0 :=
  gamma_top_eq_zero_of_slice_totalH p q₁ q₅ hS₁ hS₅ σ₁ σ₅ γ a b (cartanH_of hC N)
    htx_inj hγ hsq_b (hsplit.wu hC) u h d hd hslice

end

end Wu
end CharClass
end GroupApproximation
