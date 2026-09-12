import GroupApproximation.CharClass.ThomLIXHclassOf
import GroupApproximation.CharClass.ThomHyperplaneLHOf
import GroupApproximation.CharClass.ThomCoordinates
import GroupApproximation.CharClass.LIXKGenChern
import GroupApproximation.CharClass.LIXKGenOfBundle
import GroupApproximation.CharClass.CohomologyTotalNontrivialOf
import GroupApproximation.Meta.AxiomGuard

/-!
# The Thom class of the rank-`n` bundle pair over a field, and `hclass` over a field

Lane `lx-sliceK` (LIX strongest swarm, 2026-09-12; item S2 of `lx-stepcK-agree`'s split).

`CharClass/LIXKGenThomTerm.lean` names the Thom class of the rank-`n` mapping-torus bundle pair at
`F₂` as the preimage of the unit under `ThomDeg.thomEquiv`, and `CharClass/LIXKGenHclass.lean` shows
`jE u = π^* γ_r`.  Over a field `K` both proofs go through with two changes.

* The Leray–Hirsch statements are parameters: upstairs on `P(W ⊕ 1)` at any class `ξ` (`L`), and on
  the hyperplane at infinity at any class `ξh` restricted from `ξ` (`Lh`, `hξ`).  `LerayHirschGraded`
  is a `Prop`, so the class depends only on the classes, not on the proofs; lane `lx-lhK-b`'s compact
  Leray–Hirsch theorem over `K` discharges both.
* The zeroth Thom coordinate is `−γ_r ⌣ 1`, and over `K` the sign stays: `hclass` reads
  `jE u = π^*(−γ_r)`, with `γ_r` the hyperplane presentation's top coefficient.  Over `K` the ring Chern
  class is `−γ_r` (the monic relation negates the coefficients), so this is `π^* c_r`.  Restricting to
  the affine chart kills `ξ`, which is the hypothesis `hchart`; lane `lx-kunneth`'s
  `relToAbs_total_eq_pull_coordOf` does the collapse.

The top coefficient is the unit of `H⁰` of the base, so lane `lx-stepcK-local`'s `htop` is
`thomJmTotalOf_lixThomClassTermOf_last`, for every degree transport.

## Main declarations

* `ThomChernDeg.injective_thomJmTotalOf`, `ThomChernDeg.range_thomJmTotalOf` — the Thom data of the
  vector-bundle pair over `K`, as properties of the named coordinate map `thomJmTotalOf`.
* `KGen.lixTopCoeffOf`, `KGen.lixTopCoeffOf_ne_zero` — the unit of `H⁰`, in the top coefficient.
* `KGen.lixThomClassTermOf` — **the Thom class over `K`, as a term.**
* `KGen.thomJmTotalOf_lixThomClassTermOf`, `…_last` — its coordinates, and the top one.
* `KGen.lixThomClassTermOf_ne_zero`.
* `KGen.lixHclassOf` — **`hclass` over `K`**: `jE u = π^*(−γ_r)`.
* `KGen.lixHclassOf_of_eq` — the same at any class equal to `−γ_r`.
-/

open CategoryTheory TopologicalSpace
open scoped Matrix
open GroupApproximation.STW59
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

set_option linter.unusedSectionVars false

namespace ThomChernDeg

open LH

/-- **Precomposing with an equivalence does not change a range**, over any commutative ring. -/
theorem range_comp_linearEquivOf {K : Type} [CommRing K] {A A' N : Type} [AddCommGroup A]
    [Module K A] [AddCommGroup A'] [Module K A'] [AddCommGroup N] [Module K N]
    (φ : A ≃ₗ[K] A') (f : A' →ₗ[K] N) :
    LinearMap.range (f.comp φ.toLinearMap) = LinearMap.range f := by
  ext y
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨φ a, rfl⟩
  · rintro ⟨b, rfl⟩
    exact ⟨φ.symm b, congrArg f (φ.apply_symm_apply b)⟩

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **The coordinate map of the vector-bundle pair over a field is injective.**  The bridge is an
equivalence, reading coordinates is one, and `relToAbs` is injective at the top degree. -/
theorem injective_thomJmTotalOf (K : Type) [Field K] [CompactSpace X] [T2Space X]
    (p : Bundle X ι) {r : ℕ} (hr : 1 ≤ r)
    {ξ : Hmod K (TopCat.of (Bundle.Proj p.plusOne)) 2}
    {ξh : Hmod K (TopCat.of (Set.range (Bundle.projIncl p))) 2}
    (hξ : pull (sInclusion (Set.range (Bundle.projIncl p))) 2 ξ = ξh)
    (L : LerayHirschGraded (projMapOf p.plusOne) ξ (r + 1))
    (Lh : LerayHirschGraded (hyperProj p) ξh r) :
    Function.Injective (thomJmTotalOf K p L) := by
  have hinj0 : Function.Injective
      (relToAbs K (TopCat.of (Bundle.Proj p.plusOne)) (Set.range (Bundle.projIncl p))
        (2 * r)).hom :=
    relToAbs_injective_of_gradedOf (X := TopCat.of X) (P := TopCat.of (Bundle.Proj p.plusOne))
      (Set.range (Bundle.projIncl p)) (projMapOf p.plusOne) (hyperProj p) rfl ξ ξh hξ hr L Lh
  intro a b hab
  simp only [thomJmTotalOf_apply, thomJmOf_apply] at hab
  exact (bridgeTotalOf K p (2 * r)).injective (hinj0 ((lhTopEquivOf L).symm.injective hab))

/-- **The range of the coordinate map of the vector-bundle pair over a field is the Thom kernel.** -/
theorem range_thomJmTotalOf (K : Type) [Field K] [CompactSpace X] [T2Space X]
    (p : Bundle X ι) {r : ℕ}
    {ξ : Hmod K (TopCat.of (Bundle.Proj p.plusOne)) 2}
    {ξh : Hmod K (TopCat.of (Set.range (Bundle.projIncl p))) 2}
    (hξ : pull (sInclusion (Set.range (Bundle.projIncl p))) 2 ξ = ξh)
    (L : LerayHirschGraded (projMapOf p.plusOne) ξ (r + 1))
    (Lh : LerayHirschGraded (hyperProj p) ξh r) :
    LinearMap.range (thomJmTotalOf K p L)
      = LinearMap.ker (ThomDeg.restrictMap (R := K)
        (M := fun i : Fin (r + 1) => Hmod K (TopCat.of X) (2 * r - 2 * (i : ℕ)))
        (fun i => chernMulOf Lh i)) := by
  have h1 : LinearMap.range (thomJmTotalOf K p L)
      = LinearMap.range (thomJmOf K (lhTopEquivOf L) (Set.range (Bundle.projIncl p))) :=
    range_comp_linearEquivOf (bridgeTotalOf K p (2 * r))
      (thomJmOf K (lhTopEquivOf L) (Set.range (Bundle.projIncl p)))
  rw [h1]
  exact range_thomJm_eq_ker_restrictMapOf (X := TopCat.of X)
    (P := TopCat.of (Bundle.Proj p.plusOne)) (r := r) (Set.range (Bundle.projIncl p))
    (projMapOf p.plusOne) (hyperProj p) rfl ξ ξh hξ L Lh

end ThomChernDeg

namespace KGen

open ThomChernDeg LH

variable {ℓ : ℕ} {dd : Fin ℓ → ℕ}

/-! ## 1. The top coefficient -/

/-- The generator of the top Leray–Hirsch coefficient group over `K`: the unit of `H⁰` of the base. -/
def lixTopCoeffOf (K : Type) [Field K] (n : ℕ) (dd : Fin ℓ → ℕ) :
    Hmod K (lixN n dd) (2 * lixRank n dd - 2 * lixRank n dd) :=
  cohCast (by omega) (one (K := K) (lixN n dd))

/-- **The generator is nonzero**, because the base is nonempty. -/
theorem lixTopCoeffOf_ne_zero (K : Type) [Field K] (n : ℕ) (dd : Fin ℓ → ℕ) :
    lixTopCoeffOf K n dd ≠ 0 := by
  haveI : Nonempty ↥(lixN n dd) := inferInstanceAs (Nonempty (↥sphereOne × Gen.baseM n dd))
  have key : ∀ {m : ℕ} (h : 0 = m), cohCast h (one (K := K) (lixN n dd)) ≠ 0 := by
    intro m h
    subst h
    exact one_ne_zero_cohZeroOf K (lixN n dd)
  unfold lixTopCoeffOf
  exact key _

/-! ## 2. The Thom class -/

/-- **The Thom class of the rank-`n` mapping-torus bundle pair over a field, as a term.**  The
preimage of the unit under `ThomDeg.thomEquiv`, at the coordinate map `thomJmTotalOf K … L` and the
multiplications by the Chern coefficients of the hyperplane presentation `Lh`. -/
def lixThomClassTermOf (K : Type) [Field K] (n : ℕ)
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
    {ξ : Hmod K (TopCat.of (Bundle.Proj (lixBundle n G hGc hGu).plusOne)) 2}
    {ξh : Hmod K (TopCat.of (Set.range (Bundle.projIncl (lixBundle n G hGc hGu)))) 2}
    (hξ : pull (sInclusion (Set.range (Bundle.projIncl (lixBundle n G hGc hGu)))) 2 ξ = ξh)
    (L : LerayHirschGraded (projMapOf (lixBundle n G hGc hGu).plusOne) ξ (lixRank n dd + 1))
    (Lh : LerayHirschGraded (hyperProj (lixBundle n G hGc hGu)) ξh (lixRank n dd)) :
    ↥(relCohomology K (lixTotalPair n hGc hGu) (lixPuncturedInTotal n hGc hGu)
      (2 * lixRank n dd)) :=
  (ThomDeg.thomEquiv (M := fun i : Fin (lixRank n dd + 1) =>
      Hmod K (TopCat.of (↥sphereOne × Gen.baseM n dd)) (2 * lixRank n dd - 2 * (i : ℕ)))
    (fun i => chernMulOf Lh i)
    (thomJmTotalOf K (lixBundle n G hGc hGu) L)
    (injective_thomJmTotalOf K (lixBundle n G hGc hGu) (one_le_lixRank n dd) hξ L Lh)
    (range_thomJmTotalOf K (lixBundle n G hGc hGu) hξ L Lh)).symm (lixTopCoeffOf K n dd)

/-- **The coordinates of the Thom class over `K`**: the top one is the unit of the base, the rest are
the Chern coefficients of the hyperplane presentation acting on it, negated. -/
theorem thomJmTotalOf_lixThomClassTermOf (K : Type) [Field K] (n : ℕ)
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
    {ξ : Hmod K (TopCat.of (Bundle.Proj (lixBundle n G hGc hGu).plusOne)) 2}
    {ξh : Hmod K (TopCat.of (Set.range (Bundle.projIncl (lixBundle n G hGc hGu)))) 2}
    (hξ : pull (sInclusion (Set.range (Bundle.projIncl (lixBundle n G hGc hGu)))) 2 ξ = ξh)
    (L : LerayHirschGraded (projMapOf (lixBundle n G hGc hGu).plusOne) ξ (lixRank n dd + 1))
    (Lh : LerayHirschGraded (hyperProj (lixBundle n G hGc hGu)) ξh (lixRank n dd)) :
    thomJmTotalOf K (lixBundle n G hGc hGu) L (lixThomClassTermOf K n hGc hGu hξ L Lh)
      = ThomDeg.thomLift (M := fun i : Fin (lixRank n dd + 1) =>
          Hmod K (TopCat.of (↥sphereOne × Gen.baseM n dd)) (2 * lixRank n dd - 2 * (i : ℕ)))
          (fun i => chernMulOf Lh i) (lixTopCoeffOf K n dd) :=
  ThomDeg.jm_thomEquiv_symm
    (M := fun i : Fin (lixRank n dd + 1) =>
      Hmod K (TopCat.of (↥sphereOne × Gen.baseM n dd)) (2 * lixRank n dd - 2 * (i : ℕ)))
    (fun i => chernMulOf Lh i)
    (thomJmTotalOf K (lixBundle n G hGc hGu) L)
    (injective_thomJmTotalOf K (lixBundle n G hGc hGu) (one_le_lixRank n dd) hξ L Lh)
    (range_thomJmTotalOf K (lixBundle n G hGc hGu) hξ L Lh)
    (lixTopCoeffOf K n dd)

/-- **The top coordinate of the Thom class over `K` is the unit**, at any degree transport `h`.  This
is the `htop` of `KGen.kGenLocalNonzeroOf_of_top` and `KGen.kGenLocalNonzeroOf_of_top_closed`. -/
theorem thomJmTotalOf_lixThomClassTermOf_last (K : Type) [Field K] (n : ℕ)
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
    {ξ : Hmod K (TopCat.of (Bundle.Proj (lixBundle n G hGc hGu).plusOne)) 2}
    {ξh : Hmod K (TopCat.of (Set.range (Bundle.projIncl (lixBundle n G hGc hGu)))) 2}
    (hξ : pull (sInclusion (Set.range (Bundle.projIncl (lixBundle n G hGc hGu)))) 2 ξ = ξh)
    (L : LerayHirschGraded (projMapOf (lixBundle n G hGc hGu).plusOne) ξ (lixRank n dd + 1))
    (Lh : LerayHirschGraded (hyperProj (lixBundle n G hGc hGu)) ξh (lixRank n dd))
    (h : (0 : ℕ) = 2 * lixRank n dd - 2 * ((Fin.last (lixRank n dd) : Fin (lixRank n dd + 1)) : ℕ)) :
    thomJmTotalOf K (lixBundle n G hGc hGu) L (lixThomClassTermOf K n hGc hGu hξ L Lh)
        (Fin.last (lixRank n dd))
      = cohCast h (one (K := K) (lixN n dd)) :=
  (congrFun (thomJmTotalOf_lixThomClassTermOf K n hGc hGu hξ L Lh) (Fin.last (lixRank n dd))).trans
    (ThomDeg.thomLift_last _ _)

/-- **The Thom class over `K` is nonzero.** -/
theorem lixThomClassTermOf_ne_zero (K : Type) [Field K] (n : ℕ)
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
    {ξ : Hmod K (TopCat.of (Bundle.Proj (lixBundle n G hGc hGu).plusOne)) 2}
    {ξh : Hmod K (TopCat.of (Set.range (Bundle.projIncl (lixBundle n G hGc hGu)))) 2}
    (hξ : pull (sInclusion (Set.range (Bundle.projIncl (lixBundle n G hGc hGu)))) 2 ξ = ξh)
    (L : LerayHirschGraded (projMapOf (lixBundle n G hGc hGu).plusOne) ξ (lixRank n dd + 1))
    (Lh : LerayHirschGraded (hyperProj (lixBundle n G hGc hGu)) ξh (lixRank n dd)) :
    lixThomClassTermOf K n hGc hGu hξ L Lh ≠ 0 := by
  intro h0
  have h1 : thomJmTotalOf K (lixBundle n G hGc hGu) L (lixThomClassTermOf K n hGc hGu hξ L Lh)
      = 0 := by
    rw [h0]
    exact map_zero _
  have hc := (congrFun (thomJmTotalOf_lixThomClassTermOf K n hGc hGu hξ L Lh)
    (Fin.last (lixRank n dd))).symm.trans (congrFun h1 (Fin.last (lixRank n dd)))
  rw [ThomDeg.thomLift_last] at hc
  exact lixTopCoeffOf_ne_zero K n dd hc

/-! ## 3. `hclass` over a field -/

/-- **`hclass` over a field at rank `n`.**  The image of the Thom class under `lixJEOf` is the
pullback, along the bundle projection, of `−γ_r`, the negated top coefficient of the hyperplane
presentation `Lh`.  `hchart` says the Leray–Hirsch class upstairs dies on the affine chart. -/
theorem lixHclassOf (K : Type) [Field K] (n : ℕ)
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
    {ξ : Hmod K (TopCat.of (Bundle.Proj (lixBundle n G hGc hGu).plusOne)) 2}
    {ξh : Hmod K (TopCat.of (Set.range (Bundle.projIncl (lixBundle n G hGc hGu)))) 2}
    (hξ : pull (sInclusion (Set.range (Bundle.projIncl (lixBundle n G hGc hGu)))) 2 ξ = ξh)
    (L : LerayHirschGraded (projMapOf (lixBundle n G hGc hGu).plusOne) ξ (lixRank n dd + 1))
    (Lh : LerayHirschGraded (hyperProj (lixBundle n G hGc hGu)) ξh (lixRank n dd))
    (hchart : pull (cmap (bridgeChartIncl (lixBundle n G hGc hGu))) 2 ξ = 0) :
    (lixJEOf K n hGc hGu (2 * lixRank n dd)).hom (lixThomClassTermOf K n hGc hGu hξ L Lh)
      = (lixPiStarOf K n hGc hGu (2 * lixRank n dd)).hom (-(Lh.gamma (lixRank n dd))) := by
  have hR : 1 ≤ lixRank n dd := one_le_lixRank n dd
  refine (relToAbs_total_eq_pull_coordOf K (lixBundle n G hGc hGu) hR hchart L
    (lixThomClassTermOf K n hGc hGu hξ L Lh)).trans ?_
  have hcoord := congrFun (thomJmTotalOf_lixThomClassTermOf K n hGc hGu hξ L Lh)
    ((⟨0, hR⟩ : Fin (lixRank n dd)).castSucc)
  rw [ThomDeg.thomLift_castSucc] at hcoord
  rw [hcoord]
  have hu := chernMul_top_unitOf Lh hR
  rw [← hu]
  rfl

/-- **`hclass` over a field at any class equal to `−γ_r`**, such as the top ring Chern class
`KGen.lixChernDegOf K n dd hgen W (lixRank n dd)` once its bridge to `Lh` is proved. -/
theorem lixHclassOf_of_eq (K : Type) [Field K] (n : ℕ)
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
    {ξ : Hmod K (TopCat.of (Bundle.Proj (lixBundle n G hGc hGu).plusOne)) 2}
    {ξh : Hmod K (TopCat.of (Set.range (Bundle.projIncl (lixBundle n G hGc hGu)))) 2}
    (hξ : pull (sInclusion (Set.range (Bundle.projIncl (lixBundle n G hGc hGu)))) 2 ξ = ξh)
    (L : LerayHirschGraded (projMapOf (lixBundle n G hGc hGu).plusOne) ξ (lixRank n dd + 1))
    (Lh : LerayHirschGraded (hyperProj (lixBundle n G hGc hGu)) ξh (lixRank n dd))
    (hchart : pull (cmap (bridgeChartIncl (lixBundle n G hGc hGu))) 2 ξ = 0)
    {gamma : Hmod K (lixN n dd) (2 * lixRank n dd)}
    (hgamma : -(Lh.gamma (lixRank n dd)) = gamma) :
    (lixJEOf K n hGc hGu (2 * lixRank n dd)).hom (lixThomClassTermOf K n hGc hGu hξ L Lh)
      = (lixPiStarOf K n hGc hGu (2 * lixRank n dd)).hom gamma := by
  rw [← hgamma]
  exact lixHclassOf K n hGc hGu hξ L Lh hchart

end KGen

/-! Audited on every build. -/

#audit_axioms ThomChernDeg.injective_thomJmTotalOf
#audit_axioms ThomChernDeg.range_thomJmTotalOf
#audit_axioms KGen.lixTopCoeffOf_ne_zero
#audit_axioms KGen.thomJmTotalOf_lixThomClassTermOf
#audit_axioms KGen.thomJmTotalOf_lixThomClassTermOf_last
#audit_axioms KGen.lixThomClassTermOf_ne_zero
#audit_axioms KGen.lixHclassOf
#audit_axioms KGen.lixHclassOf_of_eq

end

end GroupApproximation.CharClass
